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

/-- Turn an `IsBoundedAtImInfty` hypothesis into an explicit uniform bound with a positive
constant. -/
lemma exists_bound_of_isBoundedAtImInfty {f : ℍ → ℂ}
    (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) :
    ∃ C A : ℝ, 0 < C ∧ ∀ z : ℍ, A ≤ z.im → ‖f z‖ ≤ C :=
  let ⟨C, A, hC⟩ := UpperHalfPlane.isBoundedAtImInfty_iff.mp hbdd
  ⟨max 1 C, A, by positivity, fun z hz => (hC z hz).trans (le_max_right _ _)⟩

/-- Exponential growth bounds for `φ₂'` and `φ₄'` on vertical rays in the upper half-plane. -/
public lemma exists_phi2'_phi4'_bound_exp :
    ∃ C A : ℝ, 0 < C ∧ ∀ z : ℍ, A ≤ z.im →
      ‖φ₂' z‖ ≤ C * Real.exp (2 * π * z.im) ∧
        ‖φ₄' z‖ ≤ C * Real.exp (2 * π * z.im) := by
  obtain ⟨CE2, AE2, _, hE2⟩ := exists_bound_of_isBoundedAtImInfty E₂_isBoundedAtImInfty
  obtain ⟨CE4, AE4, _, hE4⟩ := exists_bound_of_isBoundedAtImInfty (f := fun z : ℍ => E₄ z)
    (by simpa using ModularFormClass.bdd_at_infty E₄)
  obtain ⟨CE6, AE6, _, hE6⟩ := exists_bound_of_isBoundedAtImInfty (f := fun z : ℍ => E₆ z)
    (by simpa using ModularFormClass.bdd_at_infty E₆)
  obtain ⟨CΔ, AΔ, _, hΔ⟩ := exists_inv_Delta_bound_exp
  refine ⟨max 1 (max (CE4 ^ 2 * CΔ) (CE4 * (CE2 * CE4 + CE6) * CΔ)),
    max AΔ (max AE2 (max AE4 AE6)), by positivity, fun z hzA => ?_⟩
  have hzE2 : AE2 ≤ z.im := ((le_max_left _ _).trans (le_max_right _ _)).trans hzA
  have hzE4 : AE4 ≤ z.im :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hzA
  have hzE6 : AE6 ≤ z.im :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hzA
  have hΔz : ‖(Δ z)⁻¹‖ ≤ CΔ * Real.exp (2 * π * z.im) := hΔ z ((le_max_left _ _).trans hzA)
  have hexp_pos : 0 ≤ Real.exp (2 * π * z.im) := (Real.exp_pos _).le
  have hcore : ‖(E₂ z) * (E₄ z) - (E₆ z)‖ ≤ CE2 * CE4 + CE6 := calc
    ‖(E₂ z) * (E₄ z) - (E₆ z)‖ ≤ ‖E₂ z‖ * ‖E₄ z‖ + ‖E₆ z‖ := by
      simpa [norm_mul] using norm_sub_le ((E₂ z) * (E₄ z)) (E₆ z)
    _ ≤ CE2 * CE4 + CE6 := by gcongr <;> [exact hE2 z hzE2; exact hE4 z hzE4; exact hE6 z hzE6]
  have hφ2 : ‖φ₂' z‖ ≤ (CE4 * (CE2 * CE4 + CE6) * CΔ) * Real.exp (2 * π * z.im) := calc
    ‖φ₂' z‖ = ‖(E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) * (Δ z)⁻¹‖ := by
      simp [φ₂', div_eq_mul_inv, mul_assoc]
    _ ≤ ‖(E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z))‖ * ‖(Δ z)⁻¹‖ := norm_mul_le _ _
    _ ≤ (CE4 * (CE2 * CE4 + CE6)) * (CΔ * Real.exp (2 * π * z.im)) :=
        mul_le_mul (norm_mul_le_of_le (hE4 z hzE4) hcore) hΔz (norm_nonneg _) (by positivity)
    _ = _ := by ring
  have hφ4 : ‖φ₄' z‖ ≤ (CE4 ^ 2 * CΔ) * Real.exp (2 * π * z.im) := calc
    ‖φ₄' z‖ = ‖E₄ z‖ ^ 2 * ‖(Δ z)⁻¹‖ := by simp [φ₄', div_eq_mul_inv, pow_two]
    _ ≤ CE4 ^ 2 * (CΔ * Real.exp (2 * π * z.im)) := by gcongr; exact hE4 z hzE4
    _ = _ := by ring
  exact ⟨hφ2.trans <| mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_right _ _)) hexp_pos,
    hφ4.trans <| mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_right _ _)) hexp_pos⟩

/-- A convenient form of `φ₀_S_transform`, clearing the denominators by multiplying by `z^2`. -/
public lemma φ₀_S_transform_mul_sq (w : ℍ) :
    φ₀ (ModularGroup.S • w) * ((w : ℂ) ^ (2 : ℕ)) =
        φ₀ w * ((w : ℂ) ^ (2 : ℕ)) - (12 * Complex.I) / π * (w : ℂ) * φ₂' w -
          (36 : ℂ) / (π ^ (2 : ℕ)) * φ₄' w := by simpa using _root_.φ₀_S_transform_mul_sq w

/-- Integrability of `Φ₆'` on the imaginary axis tail `t > 1`. -/
lemma integrableOn_Φ₆'_imag_axis {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => Φ₆' u ((t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) volume := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  set b : ℝ := π * (u + 2)
  have hb : 0 < b := mul_pos Real.pi_pos (by linarith)
  refine MeasureTheory.Integrable.mono'
    (by simpa [IntegrableOn, mul_assoc] using
      ((exp_neg_integrableOn_Ioi 1 hb).const_mul C₀ :
        IntegrableOn (fun t : ℝ => C₀ * Real.exp (-b * t)) (Set.Ioi (1 : ℝ)) volume))
    (((MagicFunction.a.ComplexIntegrands.Φ₆'_contDiffOn_ℂ (r := u)).continuousOn.comp
      (by fun_prop) (fun t ht => by simpa using lt_trans zero_lt_one ht :
        Set.MapsTo (fun t : ℝ => ((t : ℂ) * Complex.I : ℂ)) (Set.Ioi (1 : ℝ))
          {z : ℂ | 0 < z.im})).aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 <| .of_forall fun t ht => ?_
  let zH : ℍ := ⟨(t : ℂ) * Complex.I, by simpa using lt_trans zero_lt_one ht⟩
  have hz_im : zH.im = t := by simp [zH, UpperHalfPlane.im]
  have hφ₀'' : ‖φ₀'' (zH : ℂ)‖ ≤ C₀ * Real.exp (-2 * π * t) := by
    simpa [φ₀''_coe_upperHalfPlane, hz_im] using
      hC₀ zH (by simpa [hz_im] using lt_trans (by norm_num : (1/2:ℝ) < 1) ht)
  refine (show ‖Φ₆' u ((t : ℂ) * Complex.I)‖ ≤
      (C₀ * Real.exp (-2 * π * t)) * Real.exp (-π * u * t) by
    rw [show Φ₆' u ((t : ℂ) * Complex.I) = φ₀'' ((t : ℂ) * Complex.I) *
        cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I)) by
      simp [MagicFunction.a.ComplexIntegrands.Φ₆']]
    refine norm_mul_le_of_le (by simpa [zH] using hφ₀'') ?_
    rw [show cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I)) =
        (Real.exp (-π * u * t) : ℂ) by ring_nf; simp [Complex.ofReal_exp],
      Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]).trans ?_
  rw [mul_assoc, ← Real.exp_add, show -2 * π * t + -π * u * t = -(b * t) by dsimp [b]; ring]

/-- Integrability of `Φ₅'` on the imaginary-axis tail `t > 1`, via `aLaplaceIntegrand`. -/
public lemma integrableOn_Φ₅'_imag_axis {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) volume := by
  have hNeg : IntegrableOn (fun t : ℝ => -aLaplaceIntegrand u t) (Set.Ioi (1 : ℝ)) volume :=
    ((aLaplaceIntegral_convergent (u := u) hu).mono_set
      fun _ ht => lt_trans (by norm_num : (0:ℝ) < 1) ht).neg
  exact hNeg.congr_fun
    (fun t _ => by simpa using (Φ₅'_imag_axis_eq_neg_aLaplaceIntegrand (u := u) (t := t)).symm)
    measurableSet_Ioi

/-- Integrability of `Φ₂'` on the imaginary-axis bounded interval `(1,A]`. -/
lemma integrableOn_Φ₂'_imag_axis_Ioc (u A : ℝ) :
    IntegrableOn (fun t : ℝ => Φ₂' u ((t : ℂ) * I)) (Set.Ioc (1 : ℝ) A) volume :=
  (((MagicFunction.a.ComplexIntegrands.Φ₁'_contDiffOn_ℂ (r := u)).continuousOn.comp
    (by fun_prop) (fun t ht => by simpa using lt_of_lt_of_le zero_lt_one ht.1 :
      Set.MapsTo (fun t : ℝ => ((t : ℂ) * I : ℂ)) (Set.Icc (1 : ℝ) A)
        {z : ℂ | 0 < z.im})).integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self

/-- Measurability of the imaginary-axis tail integrand `t ↦ Φ₂' u (tI)` on `t > A`. -/
lemma aestronglyMeasurable_Φ₂'_imag_axis_Ioi (u A : ℝ) (hA0 : 0 < A) :
    AEStronglyMeasurable (fun t : ℝ => Φ₂' u ((t : ℂ) * Complex.I))
      (volume.restrict (Set.Ioi A)) :=
  ((MagicFunction.a.ComplexIntegrands.Φ₁'_contDiffOn_ℂ (r := u)).continuousOn.comp (by fun_prop)
    fun t ht => by simpa using lt_trans hA0 ht).aestronglyMeasurable measurableSet_Ioi

/-- Modular-growth bound for `‖φ₀(S•w)‖‖w‖^2` depending only on `t = Im w`. -/
public lemma norm_phi0S_mul_sq_le {t : ℝ} (wH : ℍ) (hw_im : wH.im = t)
    {Cφ Aφ C₀ : ℝ} (hC₀_pos : 0 < C₀)
    (hC₀ : ∀ z : ℍ, (1 / 2 : ℝ) < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im))
    (hφbd : ∀ z : ℍ, Aφ ≤ z.im → ‖φ₂' z‖ ≤ Cφ * Real.exp (2 * π * z.im) ∧
      ‖φ₄' z‖ ≤ Cφ * Real.exp (2 * π * z.im))
  (ht1 : (1 : ℝ) ≤ t) (htAφ : Aφ ≤ t) (hw_norm : ‖(wH : ℂ)‖ ≤ 2 * t) :
    ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ ≤
      (4 * C₀ + (2 * c12π + c36π2) * Cφ) *
        (t ^ (2 : ℕ) * Real.exp (2 * π * t)) := by
  have hbd := hφbd wH (by simpa [hw_im] using htAφ)
  have hφ2 : ‖φ₂' wH‖ ≤ Cφ * Real.exp (2 * π * t) := by simpa [hw_im] using hbd.1
  have hφ4 : ‖φ₄' wH‖ ≤ Cφ * Real.exp (2 * π * t) := by simpa [hw_im] using hbd.2
  have htri : ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ ≤
      ‖φ₀ wH * ((wH : ℂ) ^ (2 : ℕ))‖ +
        ‖(12 * Complex.I) / π * (wH : ℂ) * φ₂' wH‖ +
          ‖(36 : ℂ) / (π ^ (2 : ℕ)) * φ₄' wH‖ := by
    rw [show φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ)) =
        φ₀ wH * ((wH : ℂ) ^ (2 : ℕ)) - (12 * Complex.I) / π * (wH : ℂ) * φ₂' wH -
          (36 : ℂ) / (π ^ (2 : ℕ)) * φ₄' wH by simpa using φ₀_S_transform_mul_sq (w := wH)]
    exact (norm_sub_le _ _).trans <| by gcongr; exact norm_sub_le _ _
  have hA : ‖φ₀ wH * ((wH : ℂ) ^ (2 : ℕ))‖ ≤
      (4 * C₀) * (t ^ (2 : ℕ) * Real.exp (2 * π * t)) :=
    calc ‖φ₀ wH * ((wH : ℂ) ^ (2 : ℕ))‖
        ≤ C₀ * (2 * t) ^ 2 := (norm_mul_le _ _).trans
          (mul_le_mul ((hC₀ wH (by rw [hw_im]; linarith)).trans
              (mul_le_of_le_one_right hC₀_pos.le (Real.exp_le_one_iff.2 <| by
                nlinarith [Real.pi_pos, wH.im_pos])))
            (by simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hw_norm 2)
            (norm_nonneg _) hC₀_pos.le)
      _ = (4 * C₀) * t ^ 2 := by ring
      _ ≤ (4 * C₀) * (t ^ 2 * Real.exp (2 * π * t)) := by
          gcongr; nlinarith [sq_nonneg t,
            Real.one_le_exp_iff.2 (show (0 : ℝ) ≤ 2 * π * t by positivity)]
  have hCφ_nonneg : 0 ≤ Cφ :=
    le_of_mul_le_mul_right (by simpa using (norm_nonneg _).trans hφ2) (Real.exp_pos _)
  have hB : ‖(12 * Complex.I) / π * (wH : ℂ) * φ₂' wH‖ ≤
      (2 * c12π * Cφ) * (t ^ (2 : ℕ) * Real.exp (2 * π * t)) :=
    calc ‖(12 * Complex.I) / π * (wH : ℂ) * φ₂' wH‖
        ≤ (c12π * ‖(wH : ℂ)‖) * ‖φ₂' wH‖ := norm_mul₃_le
      _ ≤ (c12π * (2 * t)) * (Cφ * Real.exp (2 * π * t)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hw_norm (norm_nonneg _))
            hφ2 (norm_nonneg _) (by positivity)
      _ = (2 * c12π * Cφ) * (t * Real.exp (2 * π * t)) := by ring
      _ ≤ (2 * c12π * Cφ) * (t ^ 2 * Real.exp (2 * π * t)) := by gcongr; nlinarith
  have hC : ‖(36 : ℂ) / (π ^ (2 : ℕ)) * φ₄' wH‖ ≤
      c36π2 * Cφ * (t ^ (2 : ℕ) * Real.exp (2 * π * t)) :=
    calc ‖(36 : ℂ) / (π ^ (2 : ℕ)) * φ₄' wH‖
        ≤ c36π2 * ‖φ₄' wH‖ := norm_mul_le _ _
      _ ≤ c36π2 * (Cφ * Real.exp (2 * π * t)) :=
          mul_le_mul_of_nonneg_left hφ4 (norm_nonneg _)
      _ = c36π2 * Cφ * (1 * Real.exp (2 * π * t)) := by ring
      _ ≤ c36π2 * Cφ * (t ^ 2 * Real.exp (2 * π * t)) := by gcongr; exact one_le_pow₀ ht1
  linarith [htri, hA, hB, hC]

/-- Pointwise bound for `‖Φ₂' u (tI)‖` on the tail `t ≥ 1`. -/
lemma norm_Φ₂'_imag_axis_le {u t : ℝ} {Cφ Aφ C₀ : ℝ} (hC₀_pos : 0 < C₀)
    (hC₀ : ∀ z : ℍ, (1 / 2 : ℝ) < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im))
    (hφbd : ∀ z : ℍ, Aφ ≤ z.im → ‖φ₂' z‖ ≤ Cφ * Real.exp (2 * π * z.im) ∧
      ‖φ₄' z‖ ≤ Cφ * Real.exp (2 * π * z.im))
    (ht1 : (1 : ℝ) ≤ t) (htAφ : Aφ ≤ t) :
    ‖Φ₂' u ((t : ℂ) * I)‖ ≤
      (4 * C₀ + (2 * c12π + c36π2) * Cφ) *
        (t ^ (2 : ℕ) * Real.exp (-(π * (u - 2)) * t)) := by
  set K : ℝ := 4 * C₀ + (2 * c12π + c36π2) * Cφ
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht1
  let wH : ℍ := ⟨(t : ℂ) * I + 1, by simpa using ht0⟩
  have hwH_im : wH.im = t := by simp [wH, UpperHalfPlane.im]
  have hw_norm : ‖(wH : ℂ)‖ ≤ 2 * t := (norm_add_le (_ : ℂ) _).trans <| by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg ht0.le, norm_one]; linarith
  have hdef : Φ₂' u ((t : ℂ) * I) =
      (φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))) *
        cexp ((π : ℂ) * I * (u : ℂ) * ((t : ℂ) * I)) := by
    rw [show Φ₂' u ((t : ℂ) * I) =
          (φ₀'' ((-1 : ℂ) / (((t : ℂ) * I) + 1)) * (((t : ℂ) * I + 1) ^ (2 : ℕ))) *
            cexp ((π : ℂ) * I * (u : ℂ) * ((t : ℂ) * I)) by
        simp [MagicFunction.a.ComplexIntegrands.Φ₂', MagicFunction.a.ComplexIntegrands.Φ₁',
          mul_assoc],
      show ((t : ℂ) * I + 1) = (wH : ℂ) from rfl, show φ₀ (ModularGroup.S • wH) =
        φ₀'' ((ModularGroup.S • wH : ℍ) : ℂ) by simp,
      show ((ModularGroup.S • wH : ℍ) : ℂ) = (-1 : ℂ) / (wH : ℂ) by
        simpa using ModularGroup.coe_S_smul (z := wH)]
  calc ‖Φ₂' u ((t : ℂ) * I)‖
      = ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ * Real.exp (-π * u * t) := by
        rw [hdef, norm_mul, show ‖cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I))‖ =
            Real.exp (-π * u * t) by
          rw [show cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I)) =
              (Real.exp (-π * u * t) : ℂ) by ring_nf; simp [Complex.ofReal_exp],
            Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]]
    _ ≤ (K * (t ^ (2 : ℕ) * Real.exp (2 * π * t))) * Real.exp (-π * u * t) :=
        mul_le_mul_of_nonneg_right
          (norm_phi0S_mul_sq_le wH hwH_im hC₀_pos hC₀ hφbd ht1 htAφ hw_norm) (Real.exp_pos _).le
    _ = K * (t ^ (2 : ℕ) * Real.exp (-(π * (u - 2)) * t)) := by
        rw [mul_assoc, mul_assoc, ← MagicFunction.g.CohnElkies.exp_two_pi_mul_mul_exp_neg_pi_mul]

/-- Integrability of `Φ₂'` on the imaginary-axis tail `(A,∞)` using modular bounds. -/
lemma integrableOn_Φ₂'_imag_axis_Ioi {u : ℝ} (hu : 2 < u) {Cφ Aφ C₀ A : ℝ} (hC₀_pos : 0 < C₀)
    (hC₀ : ∀ z : ℍ, (1 / 2 : ℝ) < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im))
    (hφbd : ∀ z : ℍ, Aφ ≤ z.im → ‖φ₂' z‖ ≤ Cφ * Real.exp (2 * π * z.im) ∧
      ‖φ₄' z‖ ≤ Cφ * Real.exp (2 * π * z.im))
    (hA1 : (1 : ℝ) ≤ A) (hAA : Aφ ≤ A) :
    IntegrableOn (fun t : ℝ => Φ₂' u ((t : ℂ) * I)) (Set.Ioi A) volume := by
  set a : ℝ := π * (u - 2)
  set K : ℝ := 4 * C₀ + (2 * c12π + c36π2) * Cφ
  refine MeasureTheory.Integrable.mono' (μ := volume.restrict (Set.Ioi A))
    (by simpa [IntegrableOn, mul_assoc] using
      ((integrableOn_sq_mul_exp_neg A a (mul_pos Real.pi_pos (sub_pos.mpr hu))).const_mul K :
        IntegrableOn (fun t : ℝ => K * (t ^ (2 : ℕ) * Real.exp (-a * t))) (Set.Ioi A) volume))
    (aestronglyMeasurable_Φ₂'_imag_axis_Ioi u A (lt_of_lt_of_le (by norm_num) hA1))
    ((ae_restrict_iff' measurableSet_Ioi).2 <| .of_forall fun t ht => by
      simpa [K, a] using norm_Φ₂'_imag_axis_le (u := u) hC₀_pos hC₀ hφbd
        (le_trans hA1 ht.le) (le_trans hAA ht.le))

/-- Integrability of `Φ₂'` on the imaginary-axis tail `t > 1`. -/
public lemma integrableOn_Φ₂'_imag_axis {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => Φ₂' u ((t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) volume := by
  obtain ⟨Cφ, Aφ, _, hφbd⟩ := exists_phi2'_phi4'_bound_exp
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  let A : ℝ := max 1 Aφ
  have hA1 : (1 : ℝ) ≤ A := le_max_left _ _
  simpa [(Set.Ioc_union_Ioi_eq_Ioi (a := (1 : ℝ)) (b := A) hA1).symm] using
    (integrableOn_Φ₂'_imag_axis_Ioc u A).union
      (integrableOn_Φ₂'_imag_axis_Ioi (u := u) hu (Cφ := Cφ) (Aφ := Aφ) (C₀ := C₀) (A := A)
        hC₀_pos hC₀ hφbd hA1 (le_max_right _ _))

/--
Integrability of `Φ₄'` on the imaginary-axis tail `t > 1`, via the finite-difference identity.
-/
public lemma integrableOn_Φ₄'_imag_axis {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => Φ₄' u ((t : ℂ) * I)) (Set.Ioi (1 : ℝ)) volume := by
  have h6 : IntegrableOn (fun t : ℝ => (2 : ℂ) * Φ₆' u ((t : ℂ) * I))
      (Set.Ioi (1 : ℝ)) volume := by
    simpa [mul_assoc] using (integrableOn_Φ₆'_imag_axis (u := u) hu).const_mul (2 : ℂ)
  have h5 : IntegrableOn (fun t : ℝ => (2 : ℂ) * Φ₅' u ((t : ℂ) * I))
      (Set.Ioi (1 : ℝ)) volume := by
    simpa [mul_assoc] using (integrableOn_Φ₅'_imag_axis (u := u) hu).const_mul (2 : ℂ)
  have hcomb : IntegrableOn
      (fun t : ℝ =>
        (2 : ℂ) * Φ₆' u ((t : ℂ) * I) - Φ₂' u ((t : ℂ) * I) +
          (2 : ℂ) * Φ₅' u ((t : ℂ) * I))
      (Set.Ioi (1 : ℝ)) volume :=
    (h6.sub (integrableOn_Φ₂'_imag_axis (u := u) hu)).add h5
  refine hcomb.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have hfd := Φ_finite_difference_imag_axis (u := u) (t := t) (lt_trans zero_lt_one ht)
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
  let V0 : ℂ := ∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * I)
  have hmem : ∀ {t : ℝ}, t ∈ Set.uIcc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 := fun ht => by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  have hIshift : ∀ (sign : ℂ) (zp : ℝ → ℂ) (Φⱼ : ℝ → ℂ → ℂ)
      (_ : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 → zp t = sign + (t : ℂ) * I)
      (_ : ∀ t : ℝ, Φⱼ u (sign + (t : ℂ) * I) =
        Complex.exp (sign * (((π * u : ℝ) : ℂ) * I)) * Φ₅' u ((t : ℂ) * I)),
      (∫ t in (0 : ℝ)..1, (I : ℂ) * Φⱼ u (zp t)) =
        (I : ℂ) * Complex.exp (sign * (((π * u : ℝ) : ℂ) * I)) * V0 := by
    intro sign zp Φⱼ hzp hΦ
    rw [intervalIntegral.integral_congr (g := fun t => (I : ℂ) *
      (Complex.exp (sign * (((π * u : ℝ) : ℂ) * I)) * Φ₅' u ((t : ℂ) * I)))
      fun t ht => by simp [hzp (hmem ht), hΦ, mul_assoc]]
    simp [V0, mul_assoc]
  have hI1 : MagicFunction.a.RealIntegrals.I₁' u =
      (I : ℂ) * Complex.exp (-(((π * u : ℝ) : ℂ) * I)) * V0 := by
    simpa [MagicFunction.a.RealIntegrals.I₁', MagicFunction.a.RealIntegrands.Φ₁, mul_assoc,
      neg_mul, one_mul] using hIshift (-1 : ℂ) MagicFunction.Parametrisations.z₁' Φ₁'
      (fun ht => by simpa [mul_comm] using MagicFunction.Parametrisations.z₁'_eq_of_mem ht)
      (fun t => by simpa [neg_mul, one_mul, mul_comm] using Φ₁'_shift_left (u := u) (t := t))
  have hI3 : MagicFunction.a.RealIntegrals.I₃' u =
      (I : ℂ) * Complex.exp (((π * u : ℝ) : ℂ) * I) * V0 := by
    simpa [MagicFunction.a.RealIntegrals.I₃', MagicFunction.a.RealIntegrands.Φ₃, mul_assoc,
      one_mul] using hIshift (1 : ℂ) MagicFunction.Parametrisations.z₃' Φ₃'
      (fun ht => by simpa [mul_comm] using MagicFunction.Parametrisations.z₃'_eq_of_mem ht)
      (fun t => by simpa [one_mul, mul_comm] using Φ₃'_shift_right (u := u) (t := t))
  have hI5 : MagicFunction.a.RealIntegrals.I₅' u = (-2 : ℂ) * (I : ℂ) * V0 := by
    have hparam : (∫ t in (0 : ℝ)..1, (I : ℂ) * Φ₅' u (MagicFunction.Parametrisations.z₅' t)) =
        (I : ℂ) * V0 := by
      rw [intervalIntegral.integral_congr (g := fun t => (I : ℂ) * Φ₅' u ((t : ℂ) * I)) fun t ht =>
        by simp [MagicFunction.Parametrisations.z₅'_eq_of_mem (hmem ht), mul_comm]]
      simp [V0]
    simpa [MagicFunction.a.RealIntegrals.I₅', MagicFunction.a.RealIntegrands.Φ₅, mul_assoc]
      using congrArg (fun z : ℂ => (-2 : ℂ) * z) hparam
  rw [hI1, hI3, hI5]; ring

end MagicFunction.g.CohnElkies.IntegralReps
