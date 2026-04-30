module
public import Mathlib.Init
public import
SpherePacking.MagicFunction.g.CohnElkies.AnotherIntegral.A.Cancellation.LargeImagApprox

/-!
# Integrability of the `AnotherIntegral.A` integrand

This file proves that the integrand `aAnotherIntegrand u` is integrable on `(0, ∞)` for `0 < u`.
The main work is on the tail `[1, ∞)`, where we use cancellation and exponential decay coming from
large-imaginary-part bounds for `φ₂'` and `φ₄'`.

## Main statement
* `aAnotherIntegrand_integrable_of_pos`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped Topology
open Real Complex MeasureTheory Filter
open MagicFunction.FourierEigenfunctions
open UpperHalfPlane

noncomputable section

private lemma continuousOn_phi0''_Idiv {s : Set ℝ} (hs : ∀ t ∈ s, 0 < t) :
    ContinuousOn (fun t : ℝ => φ₀'' ((Complex.I : ℂ) / (t : ℂ))) s :=
  ((by simpa [upperHalfPlaneSet] using MagicFunction.a.ComplexIntegrands.φ₀''_holo.continuousOn :
    ContinuousOn (fun z : ℂ => φ₀'' z) {z : ℂ | 0 < z.im})).comp
    (continuous_const.continuousOn.div continuous_ofReal.continuousOn
      fun t ht => by exact_mod_cast (hs t ht).ne')
    fun t ht => by simpa [imag_I_div t] using inv_pos.2 (hs t ht)

private lemma continuousOn_aBracket_of_subset_Ioi {s : Set ℝ} (hs : ∀ t ∈ s, 0 < t) :
    ContinuousOn (fun t : ℝ =>
        (((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
            ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
            ((8640 / π : ℝ) : ℂ) * t -
            ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))) s :=
  ((((by fun_prop : ContinuousOn (fun t : ℝ => ((t ^ (2 : ℕ) : ℝ) : ℂ)) s).mul
    (continuousOn_phi0''_Idiv hs)).sub (by fun_prop)).add (by fun_prop)).sub (by fun_prop)

/-! ## Asymptotic/cancellation bound for integrability on `[1,∞)`. -/

lemma exists_phi0_cancellation_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, 1 ≤ t →
        ‖(((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
              ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
              ((8640 / π : ℝ) : ℂ) * t -
              ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))‖ ≤
          C * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by
  rcases norm_φ₀_imag_le with ⟨C₀, hC₀pos, hφ₀⟩
  rcases exists_phi2'_sub_720_bound_ge with ⟨C₂, A₂, hC₂pos, hA₂, hφ₂⟩
  rcases exists_phi4'_sub_exp_sub_504_bound_ge with ⟨C₄, A₄, hC₄pos, hA₄, hφ₄⟩
  let A : ℝ := max A₂ A₄
  have hrewrite :
      ∀ {t : ℝ} (ht0 : 0 < t),
        (((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
              ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
              ((8640 / π : ℝ) : ℂ) * t -
              ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)) =
          (((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀ (zI t ht0) -
              ((12 / π : ℝ) : ℂ) * t * (φ₂' (zI t ht0) - (720 : ℂ)) +
              ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
                (φ₄' (zI t ht0) - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ))) := by
    intro t ht0
    let z : ℍ := zI t ht0
    have hzsq : (z : ℂ) ^ (2 : ℕ) = -((t ^ (2 : ℕ) : ℝ) : ℂ) := by
      dsimp [z, zI]; push_cast; rw [mul_pow]; simp
    have hcoe : ((ModularGroup.S • z : ℍ) : ℂ) = (Complex.I : ℂ) / (t : ℂ) := by
      rw [show ModularGroup.S • z = zI t⁻¹ (inv_pos.2 ht0) by
        simpa [z] using modular_S_smul_zI t ht0]; simp [zI, div_eq_mul_inv]
    have hST' :
        ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀ (ModularGroup.S • z) =
          ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀ z -
            ((12 / π : ℝ) : ℂ) * t * φ₂' z +
            ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * φ₄' z := by
      have hneg' :
          (t : ℂ) * ((t : ℂ) * φ₀ (ModularGroup.S • z)) =
            (t : ℂ) * ((t : ℂ) * φ₀ z) +
              (36 / ((π : ℂ) * (π : ℂ)) * φ₄' z +
                (Complex.I : ℂ) * 12 / (π : ℂ) * (φ₂' z * (z : ℂ))) := by
        have h0' : φ₀ (ModularGroup.S • z) * (-((t ^ (2 : ℕ) : ℝ) : ℂ)) =
            φ₀ z * (-((t ^ (2 : ℕ) : ℝ) : ℂ)) -
              (12 * Complex.I) / π * (z : ℂ) * φ₂' z - 36 / (π ^ 2) * φ₄' z := by
          simpa [hzsq] using φ₀_S_transform_mul_sq z
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
          mul_assoc, mul_left_comm, mul_comm, pow_two, neg_add, neg_mul,
          mul_neg, neg_neg] using congrArg (fun w : ℂ => -w) <|
          show φ₀ (ModularGroup.S • z) * (-((t ^ (2 : ℕ) : ℝ) : ℂ)) =
              φ₀ z * (-((t ^ (2 : ℕ) : ℝ) : ℂ)) +
                (-( (12 * Complex.I) / π * (z : ℂ) * φ₂' z)) +
                (-(36 / (π ^ 2) * φ₄' z)) by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using h0'
      have hcoeffTerm :
          (Complex.I : ℂ) * 12 / (π : ℂ) * (φ₂' z * (z : ℂ)) =
            -((t : ℂ) * ((12 : ℂ) / (π : ℂ) * φ₂' z)) := by
        dsimp [z, zI]; ring_nf; simp
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        mul_assoc, mul_left_comm, mul_comm, pow_two] using
        (by simpa [hcoeffTerm] using hneg' :
          (t : ℂ) * ((t : ℂ) * φ₀ (ModularGroup.S • z)) =
            (t : ℂ) * ((t : ℂ) * φ₀ z) +
              (36 / ((π : ℂ) * (π : ℂ)) * φ₄' z + -((t : ℂ) * ((12 : ℂ) / (π : ℂ) * φ₂' z))))
    have hSTpow :
        (↑t ^ (2 : ℕ)) * φ₀'' (Complex.I / ↑t) =
          (↑t ^ (2 : ℕ)) * φ₀ z - (12 / (π : ℂ)) * (t : ℂ) * φ₂' z +
            (36 / (π : ℂ) ^ (2 : ℕ)) * φ₄' z := by
      simpa [show φ₀'' ((Complex.I : ℂ) / (t : ℂ)) = φ₀ (ModularGroup.S • z) by
        simpa using congrArg φ₀'' hcoe.symm] using hST'
    push_cast; linear_combination hSTpow
  let Clarge : ℝ := C₀ + (12 / π) * C₂ + (36 / (π ^ (2 : ℕ))) * C₄
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ t : ℝ, 1 ≤ t → t ≤ A →
      ‖(((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
          ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
          ((8640 / π : ℝ) : ℂ) * t -
          ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))‖ ≤ M := by
    let g : ℝ → ℝ := fun t =>
      ‖(((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
          ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
          ((8640 / π : ℝ) : ℂ) * t -
          ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))‖
    have hg_cont : ContinuousOn g (Set.Icc (1 : ℝ) A) := by
      simpa [g] using (continuousOn_aBracket_of_subset_Ioi (s := Set.Icc (1 : ℝ) A)
        (fun t ht => lt_of_lt_of_le (by norm_num) ht.1)).norm
    obtain ⟨t₀, _, ht₀max⟩ :=
      isCompact_Icc.exists_isMaxOn ⟨1, le_rfl, hA₂.trans (le_max_left _ _)⟩ hg_cont
    exact ⟨g t₀, fun t ht1 htA => (isMaxOn_iff.mp ht₀max) t ⟨ht1, htA⟩⟩
  let C : ℝ := max Clarge (M / Real.exp (-2 * π * A))
  refine ⟨C, lt_of_lt_of_le (by dsimp [Clarge]; positivity) (le_max_left _ _), ?_⟩
  intro t ht1
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht1
  by_cases htA : A ≤ t
  · let z : ℍ := zI t ht0
    have hφ₀z : ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * t) := by
      simpa [show φ₀'' ((Complex.I : ℂ) * (t : ℂ)) = φ₀ z by
        simpa [z, zI] using (φ₀''_coe_upperHalfPlane z)] using hφ₀ t ht1
    have hφ₂z : ‖φ₂' z - (720 : ℂ)‖ ≤ C₂ * Real.exp (-2 * π * t) := by
      simpa [z] using hφ₂ t ht0 ((le_max_left _ _).trans htA)
    have hφ₄z : ‖φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ)‖ ≤ C₄ * Real.exp (-2 * π * t) := by
      simpa [z] using hφ₄ t ht0 ((le_max_right _ _).trans htA)
    have ht2 : (1 : ℝ) ≤ t ^ (2 : ℕ) := by nlinarith [ht1]
    have hle_t : t ≤ t ^ (2 : ℕ) := by nlinarith [ht1]
    have hexp0 : 0 ≤ Real.exp (-2 * π * t) := (Real.exp_pos _).le
    have hnorm1 : ‖((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀ z‖ ≤
        C₀ * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [hφ₀z, hC₀pos, norm_nonneg (φ₀ z), hexp0]
    have hnorm2 :
        ‖((12 / π : ℝ) : ℂ) * t * (φ₂' z - (720 : ℂ))‖ ≤
          ((12 / π) * C₂) * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) :=
      calc ‖((12 / π : ℝ) : ℂ) * t * (φ₂' z - (720 : ℂ))‖
          = (12 / π) * t * ‖φ₂' z - (720 : ℂ)‖ := by
            simp [mul_assoc, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg ht0.le, abs_of_pos Real.pi_pos]
        _ ≤ (12 / π) * t * (C₂ * Real.exp (-2 * π * t)) := by gcongr
        _ ≤ (12 / π) * (t ^ (2 : ℕ)) * (C₂ * Real.exp (-2 * π * t)) := by
            simpa [mul_assoc] using mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hle_t (mul_nonneg hC₂pos.le hexp0)) (by positivity)
        _ = ((12 / π) * C₂) * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by ring
    have hnorm3 :
        ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
            (φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ))‖ ≤
          ((36 / (π ^ (2 : ℕ))) * C₄) * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) :=
      calc ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
            (φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ))‖
          = (36 / (π ^ (2 : ℕ))) * ‖φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ)‖ := by
            simp [Complex.norm_real, Real.norm_eq_abs]
        _ ≤ (36 / (π ^ (2 : ℕ))) * (C₄ * Real.exp (-2 * π * t)) := by gcongr
        _ ≤ (36 / (π ^ (2 : ℕ))) * (t ^ (2 : ℕ)) * (C₄ * Real.exp (-2 * π * t)) := by
            simpa [one_mul, mul_assoc] using mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right ht2 (mul_nonneg hC₄pos.le hexp0)) (by positivity)
        _ = ((36 / (π ^ (2 : ℕ))) * C₄) * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by ring
    have htri : ‖(((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
          ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
          ((8640 / π : ℝ) : ℂ) * t -
          ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))‖ ≤
        Clarge * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) := by
      set x : ℂ := ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀ z
      set y : ℂ := ((12 / π : ℝ) : ℂ) * t * (φ₂' z - (720 : ℂ))
      set z' : ℂ := ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) *
        (φ₄' z - (Real.exp (2 * π * t) : ℂ) - (504 : ℂ))
      rw [show (((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
          ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
          ((8640 / π : ℝ) : ℂ) * t -
          ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)) = x - y + z' by simpa [x, y, z'] using hrewrite ht0]
      refine (((norm_add_le _ _).trans (by linarith [norm_sub_le x y, norm_nonneg z'])).trans
        (add_le_add_three hnorm1 hnorm2 hnorm3)).trans ?_
      dsimp [Clarge]; nlinarith [hexp0, sq_nonneg t]
    exact htri.trans (by gcongr; exact le_max_left _ _)
  · have htA' : t ≤ A := le_of_not_ge htA
    have hbound := hM t ht1 htA'
    have hexp_le : Real.exp (-2 * π * A) ≤ (t ^ (2 : ℕ)) * Real.exp (-2 * π * t) :=
      (Real.exp_le_exp.2 <| mul_le_mul_of_nonpos_left htA' (by nlinarith [Real.pi_pos])).trans <| by
        simpa using mul_le_mul_of_nonneg_right (by nlinarith [ht1] : (1 : ℝ) ≤ t ^ (2 : ℕ))
          (Real.exp_pos _).le
    have hscale : M ≤ (M / Real.exp (-2 * π * A)) * ((t ^ (2 : ℕ)) * Real.exp (-2 * π * t)) := by
      simpa [show (M / Real.exp (-2 * π * A)) * Real.exp (-2 * π * A) = M by
        field_simp [Real.exp_ne_zero]] using mul_le_mul_of_nonneg_left hexp_le
        (div_nonneg (le_trans (norm_nonneg _) hbound) (Real.exp_pos (-2 * π * A)).le)
    nlinarith [hbound, hscale, mul_le_mul_of_nonneg_right (le_max_right Clarge _ : _ ≤ C)
      (by positivity : (0 : ℝ) ≤ (t ^ (2 : ℕ)) * Real.exp (-2 * π * t))]

/-! ## Integrability of the "another integrand" for `0 < u`. -/

private lemma continuousOn_aAnotherIntegrand_of_subset_Ioi
    {s : Set ℝ} (hs : ∀ t ∈ s, 0 < t) (u : ℝ) :
    ContinuousOn (fun t : ℝ => aAnotherIntegrand u t) s :=
  ((((by fun_prop : Continuous fun t : ℝ => ((t ^ (2 : ℕ) : ℝ) : ℂ)).continuousOn.mul
    (continuousOn_phi0''_Idiv hs)).sub (by fun_prop) |>.add (by fun_prop)).sub (by fun_prop)).mul
      (by fun_prop : Continuous fun t : ℝ => ((Real.exp (-π * u * t)) : ℂ)).continuousOn

lemma aAnotherIntegrand_integrableOn_Ioc {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => aAnotherIntegrand u t) (Set.Ioc (0 : ℝ) 1) := by
  rcases MagicFunction.PolyFourierCoeffBound.norm_φ₀_le with ⟨Cφ₀, hCφ₀_pos, hCφ₀⟩
  let M : ℝ := Cφ₀ + ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ * Real.exp (2 * π) +
    ‖((8640 / π : ℝ) : ℂ)‖ + ‖((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖
  refine MeasureTheory.IntegrableOn.of_bound (by simp : (volume : Measure ℝ) (Set.Ioc 0 1) < ⊤)
    ((continuousOn_aAnotherIntegrand_of_subset_Ioi (fun t ht => ht.1) u).aestronglyMeasurable
      measurableSet_Ioc) M
    ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht => ?_))
  have ht0 : 0 < t := ht.1
  have him_pos : 0 < (((Complex.I : ℂ) / (t : ℂ)) : ℂ).im := by
    simpa [imag_I_div t] using inv_pos.2 ht0
  let z : ℍ := ⟨(Complex.I : ℂ) / (t : ℂ), him_pos⟩
  have hzHalf : (1 / 2 : ℝ) < z.im := by
    linarith [(by simpa [z, UpperHalfPlane.im, imag_I_div t] using (one_le_inv₀ ht0).2 ht.2 :
      (1 : ℝ) ≤ z.im)]
  have hφ0'' : ‖φ₀'' ((Complex.I : ℂ) / (t : ℂ))‖ ≤ Cφ₀ := by
    simpa [show φ₀ z = φ₀'' ((Complex.I : ℂ) / (t : ℂ)) by
      simpa [z] using (φ₀''_def (z := (Complex.I : ℂ) / (t : ℂ)) him_pos).symm] using
      (hCφ₀ z hzHalf).trans
        (by simpa using mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2
          (by nlinarith [Real.pi_pos, (z.2).le])) hCφ₀_pos.le)
  have ht2_le : (t ^ (2 : ℕ) : ℝ) ≤ 1 := by nlinarith [ht0.le, ht.2]
  have hbr : ‖(((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
          ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
          ((8640 / π : ℝ) : ℂ) * t -
          ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))‖ ≤
      (t ^ (2 : ℕ) : ℝ) * Cφ₀ +
        ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ * Real.exp (2 * π) +
        ‖((8640 / π : ℝ) : ℂ)‖ + ‖((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ := by
    set A : ℂ := ((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ))
    set B : ℂ := ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t)
    set Cc : ℂ := ((8640 / π : ℝ) : ℂ) * t
    set D : ℂ := ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ)
    have ht2nn : (0 : ℝ) ≤ t ^ (2 : ℕ) := by positivity
    have hA : ‖A‖ ≤ (t ^ (2 : ℕ) : ℝ) * Cφ₀ := by
      simpa [A, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht2nn]
        using mul_le_mul_of_nonneg_left hφ0'' ht2nn
    have hB : ‖B‖ ≤ ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ * Real.exp (2 * π) := by
      rw [show ‖B‖ = ‖((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ)‖ * Real.exp (2 * π * t) by
        simp [-Complex.ofReal_exp, B]]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (by nlinarith [Real.pi_pos, ht.2])) (norm_nonneg _)
    have hC : ‖Cc‖ ≤ ‖((8640 / π : ℝ) : ℂ)‖ := by
      simpa [Cc, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0.le] using
        mul_le_mul_of_nonneg_left ht.2 (norm_nonneg ((8640 / π : ℝ) : ℂ))
    linarith [((show ‖A - B + Cc - D‖ = ‖(A - B) + (Cc - D)‖ by ring_nf).le.trans
      (norm_add_le _ _)).trans (add_le_add (norm_sub_le _ _) (norm_sub_le _ _))]
  have hmul : ‖aAnotherIntegrand u t‖ ≤
      ‖(((t ^ (2 : ℕ) : ℝ) : ℂ) * φ₀'' ((Complex.I : ℂ) / (t : ℂ)) -
            ((36 / (π ^ (2 : ℕ)) : ℝ) : ℂ) * Real.exp (2 * π * t) +
            ((8640 / π : ℝ) : ℂ) * t -
            ((18144 / (π ^ (2 : ℕ)) : ℝ) : ℂ))‖ := by
    simpa [aAnotherIntegrand, norm_mul, mul_assoc] using mul_le_mul_of_nonneg_left
      (by rw [norm_ofReal_exp]; exact Real.exp_le_one_iff.2 (by
        nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hu.le) ht0.le]) :
        ‖(Real.exp (-π * u * t) : ℂ)‖ ≤ 1) (norm_nonneg _)
  nlinarith [hmul.trans hbr, mul_le_mul_of_nonneg_right ht2_le hCφ₀_pos.le]

lemma aAnotherIntegrand_integrableOn_Ici {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => aAnotherIntegrand u t) (Set.Ici (1 : ℝ)) := by
  rcases exists_phi0_cancellation_bound with ⟨C, _, hC⟩
  have hbound : ∀ t : ℝ, t ∈ Set.Ici (1 : ℝ) → ‖aAnotherIntegrand u t‖ ≤
      C * (t ^ (2 : ℕ)) * Real.exp (-(2 * π + π * u) * t) := fun t ht => by
    rw [show C * (t ^ (2 : ℕ)) * Real.exp (-(2 * π + π * u) * t) =
      (C * (t ^ (2 : ℕ)) * Real.exp (-2 * π * t)) * Real.exp (-π * u * t) by
        rw [mul_assoc (C * _), ← Real.exp_add]; ring_nf]
    simpa [-Complex.ofReal_exp, aAnotherIntegrand, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right (hC t ht) (Real.exp_pos (-π * u * t)).le
  have ha : 0 < (2 * π + π * u) / 2 := by positivity
  have hdom :
      IntegrableOn (fun t : ℝ => C * (t ^ (2 : ℕ)) * Real.exp (-(2 * π + π * u) * t))
        (Set.Ici (1 : ℝ)) := by
    set b : ℝ := (2 * π + π * u) / 2
    have hExpRef : (fun t : ℝ => Real.exp (-b * t)) =O[atTop]
        fun t : ℝ => Real.exp (-b * t) := Asymptotics.isBigO_refl _ _
    have hfacBig : (fun t : ℝ => (C * (t ^ (2 : ℕ) : ℝ)) * Real.exp (-b * t)) =O[atTop]
        fun _t : ℝ => (1 : ℝ) :=
      ((((isLittleO_pow_exp_pos_mul_atTop 2 ha).const_mul_left C :
        (fun t : ℝ => C * (t ^ (2 : ℕ) : ℝ)) =o[atTop]
          fun t : ℝ => Real.exp (b * t)).mul_isBigO hExpRef).congr_right
        (fun t => by rw [← Real.exp_add]; simp)).isBigO
    exact (integrableOn_Ici_iff_integrableOn_Ioi (μ := (volume : Measure ℝ))
        (b := (1 : ℝ))).2 <| integrable_of_isBigO_exp_neg (a := 1) (b := b) ha
        (by simpa [Set.Ici] using (by fun_prop :
          ContinuousOn (fun t : ℝ => C * (t ^ (2 : ℕ)) * Real.exp (-(2 * π + π * u) * t))
            (Set.Ici (1 : ℝ))))
        (((hfacBig.mul hExpRef).congr_left fun t => by
          rw [mul_assoc, ← Real.exp_add]; congr 1; dsimp [b]; ring_nf).congr_right fun _ => by ring)
  exact MeasureTheory.Integrable.mono' hdom.integrable
    ((continuousOn_aAnotherIntegrand_of_subset_Ioi
      (fun t ht => lt_of_lt_of_le (by norm_num) ht) u).aestronglyMeasurable measurableSet_Ici)
    ((ae_restrict_iff' measurableSet_Ici).2 (Filter.Eventually.of_forall hbound))

/-- For `u > 0`, the function `t ↦ aAnotherIntegrand u t` is integrable on `(0, ∞)`. -/
public lemma aAnotherIntegrand_integrable_of_pos {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => aAnotherIntegrand u t) (Set.Ioi (0 : ℝ)) := by
  rw [← Set.Ioc_union_Ici_eq_Ioi (a := (0 : ℝ)) (b := 1) zero_lt_one]
  exact (aAnotherIntegrand_integrableOn_Ioc hu).union (aAnotherIntegrand_integrableOn_Ici hu)

end

end MagicFunction.g.CohnElkies.IntegralReps
