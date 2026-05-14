module
public import SpherePacking.MagicFunction.b.Basic
public import SpherePacking.MagicFunction.b.PsiBounds
public import SpherePacking.MagicFunction.b.Schwartz.PsiExpBounds.PsiSDecay

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.ForMathlib.IntegrablePowMulExp
import SpherePacking.Integration.DifferentiationUnderIntegral
import SpherePacking.Integration.SmoothIntegralIciOne
import SpherePacking.ForMathlib.IteratedDeriv
import SpherePacking.Integration.Measure
import SpherePacking.MagicFunction.PsiTPrimeZ1
import Mathlib.Topology.Order.ProjIcc

/-! # Smoothness and decay for `J₁'` and `J₆'`.

* `J₁'`: `ψT'_z₁'_eq`, `contDiff_J₁'`, `decay_J₁'`.
* `J₆'` (merged from `SmoothJ6.Bounds`): `gN_J6_integrand` integrability, `contDiffOn_J₆'_Ioi_neg1`,
  `decay_J₆'`. -/

namespace SpherePacking.Integration

noncomputable section

open Complex Real Set MeasureTheory Filter

/-- The `n`-th `x`-derivative integrand appearing in `J₆'`-type formulas. -/
@[expose] public def gN_J6_integrand (f : ℝ → ℂ) (n : ℕ) (x : ℝ) : ℝ → ℂ :=
  fun t : ℝ ↦ ((-Real.pi * t : ℂ) ^ n) *
    ((Complex.I : ℂ) * (f t * cexp ((x : ℂ) * (-Real.pi * t : ℂ))))

/-- Integrability of `gN_J6_integrand` on `Ici 1` under an exponential bound on `f`. -/
public lemma integrable_gN_J6 (f : ℝ → ℂ)
    (hBound : ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C * Real.exp (-Real.pi * t))
    (n : ℕ) (x : ℝ) (hx : -1 < x)
    (hmeas : AEStronglyMeasurable (gN_J6_integrand f n x)
        ((volume : Measure ℝ).restrict (Ici (1 : ℝ)))) :
    Integrable (gN_J6_integrand f n x) ((volume : Measure ℝ).restrict (Ici (1 : ℝ))) := by
  rcases hBound with ⟨C, hC⟩
  have hC_nonneg : 0 ≤ C :=
    ForMathlib.nonneg_of_nonneg_le_mul (a := ‖f 1‖) (b := Real.exp (-Real.pi * (1 : ℝ)))
      (C := C) (norm_nonneg _) (by positivity) (by simpa using hC 1 le_rfl)
  have hb : 0 < Real.pi * (x + 1) := mul_pos Real.pi_pos (by linarith)
  let bound : ℝ → ℝ :=
    fun t ↦ (Real.pi ^ n) * (t ^ n * Real.exp (-(Real.pi * (x + 1)) * t)) * C
  have hbound_int : Integrable bound ((volume : Measure ℝ).restrict (Ici (1 : ℝ))) := by
    simpa [bound, IntegrableOn, mul_assoc, mul_left_comm, mul_comm] using
      (ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := n) (b := Real.pi * (x + 1))
        (by simpa [mul_assoc] using hb)).const_mul ((Real.pi ^ n) * C)
  refine Integrable.mono' hbound_int hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun t ht ↦ ?_
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  calc
    ‖gN_J6_integrand f n x t‖
        = (Real.pi * t) ^ n * (‖f t‖ * Real.exp (-Real.pi * x * t)) := by
          simp [gN_J6_integrand, norm_pow, Complex.norm_exp, Real.norm_eq_abs,
            abs_of_pos Real.pi_pos, abs_of_nonneg ht0, mul_left_comm, mul_comm]
    _ ≤ (Real.pi * t) ^ n * ((C * Real.exp (-Real.pi * t)) * Real.exp (-Real.pi * x * t)) := by
          gcongr; exact hC t ht
    _ = bound t := by
          change (Real.pi * t) ^ n * ((C * Real.exp (-Real.pi * t)) * Real.exp (-Real.pi * x * t)) =
            (Real.pi ^ n) * (t ^ n * Real.exp (-(Real.pi * (x + 1)) * t)) * C
          rw [show (-(Real.pi * (x + 1)) * t) = (-Real.pi * t) + (-Real.pi * x * t) by ring,
            Real.exp_add]; ring

end

end SpherePacking.Integration

namespace MagicFunction.b.Schwartz.J6Smooth

noncomputable section

open scoped Topology ContDiff
open Complex Real Set MeasureTheory Filter MagicFunction.Parametrisations
  MagicFunction.b.RealIntegrals MagicFunction.b.PsiBounds
  MagicFunction.b.PsiBounds.PsiExpBounds SpherePacking.ForMathlib SpherePacking.Integration

def μ : Measure ℝ := μIciOne
def s : Set ℝ := Ioi (-1 : ℝ)

lemma isOpen_s : IsOpen s := isOpen_Ioi

abbrev coeff (t : ℝ) : ℂ := SmoothIntegralIciOne.coeff t
abbrev g (x t : ℝ) : ℂ := SmoothIntegralIciOne.g (hf := ψS.resToImagAxis) x t
abbrev gN (n : ℕ) (x t : ℝ) : ℂ := SmoothIntegralIciOne.gN (hf := ψS.resToImagAxis) n x t

lemma gN_measurable (n : ℕ) (x : ℝ) : AEStronglyMeasurable (gN n x) (μ) := by
  have hcoeff : Continuous coeff := by
    simpa [coeff] using (continuous_const.mul Complex.continuous_ofReal : Continuous fun t : ℝ =>
      (-Real.pi : ℂ) * (t : ℂ))
  refine (ContinuousOn.aestronglyMeasurable (μ := (volume : Measure ℝ))
    (s := Ici (1 : ℝ)) ?_ measurableSet_Ici).mono_measure (by simp [μ, μIciOne])
  simpa [gN] using (hcoeff.pow n).continuousOn.mul
    (by simpa [g, mul_assoc] using (continuousOn_const.mul
      ((Function.continuousOn_resToImagAxis_Ici_one_of (F := ψS) continuous_ψS).mul
        ((continuous_const.mul hcoeff).cexp).continuousOn)) :
      ContinuousOn (g x) (Ici (1 : ℝ)))

lemma gN_integrable (n : ℕ) (x : ℝ) (hx : x ∈ s) : Integrable (gN n x) μ := by
  simpa [μ, μIciOne] using
    (integrable_gN_J6 (f := ψS.resToImagAxis)
      (hBound := exists_bound_norm_ψS_resToImagAxis_exp_Ici_one)
      (n := n) (x := x) hx (hmeas := gN_measurable (n := n) (x := x)))

def F (n : ℕ) (x : ℝ) : ℂ := ∫ t in Ici (1 : ℝ), gN n x t

/-- `G` incorporates the outer `-2` factor from the definition of `J₆'`. -/
def G (n : ℕ) (x : ℝ) : ℂ := (-2 : ℂ) * F n x

lemma hasDerivAt_F (n : ℕ) (x : ℝ) (hx : x ∈ s) :
    HasDerivAt (fun y : ℝ => F n y) (F (n + 1) x) x := by
  simpa [F, μ] using
    (SmoothIntegralIciOne.hasDerivAt_integral_gN
      (hf := ψS.resToImagAxis) (shift := (1 : ℝ))
      (exists_bound_norm_hf := by
        simpa [one_mul, mul_assoc] using exists_bound_norm_ψS_resToImagAxis_exp_Ici_one)
      (gN_measurable := fun n x => by simpa [μ] using gN_measurable (n := n) (x := x))
      (n := n) (x := x) hx (hF_int := by simpa [μ] using gN_integrable (n := n) (x := x) hx))

lemma iteratedDeriv_G_eq : ∀ n m : ℕ, Set.EqOn (iteratedDeriv n (G m)) (G (n + m)) s := by
  intro n
  induction n with
  | zero => intro m x _; simp [iteratedDeriv_zero]
  | succ n ih =>
      intro m x hx
      have hEq : iteratedDeriv n (G m) =ᶠ[𝓝 x] G (n + m) := by
        filter_upwards [isOpen_s.mem_nhds hx] with y hy using ih (m := m) hy
      simpa [iteratedDeriv_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Filter.EventuallyEq.deriv_eq hEq).trans
          ((by simpa [G] using (hasDerivAt_F (n := n + m) (x := x) hx).const_mul (-2 : ℂ) :
            HasDerivAt (fun y : ℝ => G (n + m) y) (G (n + m + 1) x) x).deriv)

private lemma J₆'_eq_G0 (x : ℝ) : RealIntegrals.J₆' x = G 0 x := by
  have hint : (∫ t in Ici (1 : ℝ),
          (Complex.I : ℂ) * ψS' (z₆' t) * cexp (π * (Complex.I : ℂ) * x * (z₆' t))) =
        ∫ t in Ici (1 : ℝ), g x t := by
    refine integral_congr_ae <| (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun t ht => ?_
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    have hz : z₆' t = (Complex.I : ℂ) * t := z₆'_eq_of_mem ht
    dsimp
    rw [show ψS' (z₆' t) = ψS.resToImagAxis t by
      simp [ψS', Function.resToImagAxis, ResToImagAxis, hz, ht0, mul_comm],
      show cexp ((π : ℂ) * (Complex.I : ℂ) * (x : ℂ) * (z₆' t)) = cexp ((x : ℂ) * coeff t) from
        congrArg cexp (by simp [coeff, SmoothIntegralIciOne.coeff, hz]; ring_nf; simp)]
    simp [g, SmoothIntegralIciOne.g, Function.resToImagAxis, ResToImagAxis, mul_assoc]
  simpa [G, F, gN, SmoothIntegralIciOne.gN, g, RealIntegrals.J₆', mul_assoc, mul_left_comm,
    mul_comm] using congrArg (fun J : ℂ => (-2 : ℂ) * J) hint

/-- Smoothness of `RealIntegrals.J₆'` on the open half-line `Ioi (-1)`. -/
public theorem contDiffOn_J₆'_Ioi_neg1 :
    ContDiffOn ℝ ∞ RealIntegrals.J₆' (Ioi (-1 : ℝ)) :=
  (by simpa [G] using contDiffOn_const.mul (by simpa using
      (SpherePacking.ForMathlib.contDiffOn_family_infty_of_hasDerivAt (F := F) (s := s) isOpen_s
        (fun n x hx => by simpa using (hasDerivAt_F (n := n) (x := x) hx)) 0)) :
    ContDiffOn ℝ ∞ (G 0) s).congr (fun x _ => J₆'_eq_G0 x)

/-- Schwartz-type decay bounds for `RealIntegrals.J₆'` and its iterated derivatives on `0 ≤ x`. -/
public theorem decay_J₆' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₆' x‖ ≤ C := by
  intro k n
  obtain ⟨B, hB⟩ :=
    SpherePacking.ForMathlib.exists_bound_pow_mul_exp_neg_mul (k := k) (b := Real.pi) Real.pi_pos
  obtain ⟨Cψ, hCψ⟩ := exists_bound_norm_ψS_resToImagAxis_exp_Ici_one
  have hCψ0 : 0 ≤ Cψ := SpherePacking.ForMathlib.nonneg_of_nonneg_le_mul (a := ‖ψS.resToImagAxis 1‖)
    (b := Real.exp (-Real.pi * (1 : ℝ))) (C := Cψ) (norm_nonneg _) (by positivity)
    (by simpa using hCψ 1 le_rfl)
  let bound : ℝ → ℝ := fun t ↦ (Real.pi ^ n) * (t ^ n * Real.exp (-Real.pi * t)) * Cψ
  have hbound_int : Integrable bound μ := by
    simpa [bound, mul_assoc, mul_left_comm, mul_comm, IntegrableOn, μ, μIciOne] using
      (SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := n) (b := Real.pi)
        Real.pi_pos).const_mul ((Real.pi ^ n) * Cψ)
  let Kn : ℝ := ∫ t, bound t ∂μ
  have hKn_nonneg : 0 ≤ Kn := integral_nonneg_of_ae <|
    (ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Ici).2 <| .of_forall fun t ht => by
      have : 0 ≤ t := zero_le_one.trans ht; positivity
  refine ⟨2 * Kn * B, fun x hx => ?_⟩
  have hGbound : ‖G n x‖ ≤ 2 * Kn * Real.exp (-Real.pi * x) := by
    have hbound_ae :
        ∀ᵐ t ∂μ, ‖gN n x t‖ ≤ bound t * Real.exp (-Real.pi * x) := by
      refine (ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Ici).2 <| .of_forall ?_
      intro t ht
      have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1) ht
      have hxexp : Real.exp (-Real.pi * x * t) ≤ Real.exp (-Real.pi * x) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          Real.exp_le_exp.2 (neg_le_neg (le_mul_of_one_le_right
            (mul_nonneg Real.pi_pos.le hx) ht))
      calc
        ‖gN n x t‖ = ‖coeff t‖ ^ n * ‖g x t‖ := by
              simp [gN, SmoothIntegralIciOne.gN, g, coeff, norm_pow]
        _ ≤ (Real.pi * t) ^ n * (‖ψS.resToImagAxis t‖ * Real.exp (-Real.pi * x * t)) := by
              gcongr ?_ * ?_
              · simp [coeff, SmoothIntegralIciOne.coeff_norm (t := t) ht]
              · simpa [g] using SmoothIntegralIciOne.g_norm_bound
                  (hf := ψS.resToImagAxis) (x := x) (t := t)
        _ ≤ (Real.pi * t) ^ n * ((Cψ * Real.exp (-Real.pi * t)) * Real.exp (-Real.pi * x)) := by
              gcongr; exact hCψ t ht
        _ = bound t * Real.exp (-Real.pi * x) := by ring
    have hFn : ‖F n x‖ ≤ Kn * Real.exp (-Real.pi * x) := calc
      ‖F n x‖ ≤ ∫ t, ‖gN n x t‖ ∂μ := by
            simpa [show F n x = ∫ t, gN n x t ∂μ by simp [F, μ, μIciOne]] using
              (norm_integral_le_integral_norm (μ := μ) (f := gN n x))
      _ ≤ ∫ t, bound t * Real.exp (-Real.pi * x) ∂μ :=
            integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg (gN n x t))
              (by simpa [mul_assoc, mul_left_comm, mul_comm] using
                hbound_int.mul_const (Real.exp (-Real.pi * x))) hbound_ae
      _ = Kn * Real.exp (-Real.pi * x) := by simpa [Kn] using
            (integral_mul_const (μ := μ) (r := Real.exp (-Real.pi * x)) (f := bound))
    calc ‖G n x‖
        ≤ 2 * (Kn * Real.exp (-Real.pi * x)) := by
          simpa [G, norm_mul, mul_assoc] using
            mul_le_mul_of_nonneg_left hFn (by positivity : (0 : ℝ) ≤ 2)
      _ = 2 * Kn * Real.exp (-Real.pi * x) := by ring
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₆' x‖
        = x ^ k * ‖G n x‖ := by
          simp [Real.norm_of_nonneg hx, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
            show iteratedDeriv n RealIntegrals.J₆' x = G n x by
              simpa [show RealIntegrals.J₆' = G 0 from funext J₆'_eq_G0] using
                (iteratedDeriv_G_eq (n := n) (m := 0))
                  (lt_of_lt_of_le (by norm_num) hx : x ∈ s)]
    _ ≤ x ^ k * (2 * Kn * Real.exp (-Real.pi * x)) := by gcongr
    _ = (2 * Kn) * (x ^ k * Real.exp (-Real.pi * x)) := by ring
    _ ≤ (2 * Kn) * B :=
      mul_le_mul_of_nonneg_left (hB x hx) (by positivity)

end

end MagicFunction.b.Schwartz.J6Smooth

namespace MagicFunction.b.Schwartz.J1Smooth

noncomputable section

open scoped Interval Manifold Topology UpperHalfPlane MatrixGroups ModularForm
open Complex Real Set MeasureTheory Filter intervalIntegral UpperHalfPlane
open MagicFunction.Parametrisations MagicFunction.b.RealIntegrals MagicFunction.b.PsiBounds
open Matrix ModularGroup ModularForm

def μ : Measure ℝ := SpherePacking.Integration.μIoo01

attribute [irreducible] μ

instance : IsFiniteMeasure μ :=
  ⟨by simp [μ, SpherePacking.Integration.μIoo01, Measure.restrict_apply, MeasurableSet.univ]⟩

def coeff (t : ℝ) : ℂ := ((π : ℂ) * (Complex.I : ℂ)) * z₁' t

def hf (t : ℝ) : ℂ := (Complex.I : ℂ) * ψT' (z₁' t)

def gN (n : ℕ) (x t : ℝ) : ℂ :=
  SpherePacking.Integration.DifferentiationUnderIntegral.gN (coeff := coeff) (hf := hf) n x t

lemma coeff_norm_le (t : ℝ) : ‖coeff t‖ ≤ 2 * π := by
  simpa [coeff, mul_assoc] using
    SpherePacking.ForMathlib.norm_mul_pi_I_le_two_pi (z := z₁' t) (hz := norm_z₁'_le_two t)

/-- Modular rewrite for `ψT' (z₁' t)`, used to control the integrand near `t = 0`. -/
public lemma ψT'_z₁'_eq (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    ψT' (z₁' t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ (2 : ℕ) := by
  have ht0 : 0 < t := ht.1
  have hz_im : 0 < (z₁' t).im := im_z₁'_pos (t := t) ht
  let z : ℍ := ⟨z₁' t, hz_im⟩
  have hψT : ψT z = ψS ((S * T) • z) * (z + 1 : ℂ) ^ (2 : ℕ) := by
    simpa using ((by simpa using congrArg (fun f : ℍ → ℂ => f z) ψS_slash_ST :
      (ψS ∣[(-2 : ℤ)] (S * T)) z = ψT z).symm.trans (by simpa using slashST' (z := z) (F := ψS)))
  have hzplus : (z + 1 : ℂ) = (Complex.I : ℂ) * (t : ℂ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm, add_left_comm, add_comm] using
      congrArg (fun w : ℂ => w + (1 : ℂ)) (z₁'_eq_of_mem (t := t) (mem_Icc_of_Ioc ht))
  have hsmul : (S * T) • z = (⟨(Complex.I : ℂ) * (1 / t), by simp [ht0]⟩ : ℍ) := by
    ext1
    rw [coe_ST_smul (z := z), show ((z : ℂ) + 1) = (Complex.I : ℂ) * (t : ℂ) from hzplus]
    field_simp [show (t : ℂ) ≠ 0 by exact_mod_cast ne_of_gt ht0, Complex.I_ne_zero]; simp
  have hψS' : ψS ((S * T) • z) = ψS.resToImagAxis (1 / t) := by
    rw [hsmul]; simp [Function.resToImagAxis, ResToImagAxis, ht0]
  have heq : ψT' (z₁' t) = ψT z := by simp [ψT', hz_im, z]
  rw [hψS', hzplus] at hψT
  simpa [heq] using hψT

lemma continuous_coeff : Continuous coeff := by
  simpa [coeff, mul_assoc] using continuous_const.mul continuous_z₁'

lemma continuousOn_hf :
    ContinuousOn hf (Ioo (0 : ℝ) 1) := by
  simpa [hf] using
    (continuousOn_const.mul <| by
      simpa using
        MagicFunction.continuousOn_ψT'_z₁'_of (k := 2) (ψS := ψS) (ψT' := ψT')
          (Function.continuousOn_resToImagAxis_Ici_one_of (F := ψS) continuous_ψS)
          ψT'_z₁'_eq)

lemma exists_bound_norm_hf : ∃ M, ∀ t ∈ Ioo (0 : ℝ) 1, ‖hf t‖ ≤ M :=
  let ⟨Mψ, hMψ⟩ := MagicFunction.exists_bound_norm_ψT'_z₁'_of (k := 2) (ψS := ψS) (ψT' := ψT')
    exists_bound_norm_ψS_resToImagAxis_Ici_one ψT'_z₁'_eq
  ⟨Mψ, fun t ht => by simpa [hf] using hMψ t ht⟩

def I (n : ℕ) (x : ℝ) : ℂ := ∫ t, gN n x t ∂μ

lemma hasDerivAt_integral_gN (n : ℕ) (x₀ : ℝ) :
    HasDerivAt (fun x : ℝ ↦ I n x) (I (n + 1) x₀) x₀ := by
  simpa [I, μ, SpherePacking.Integration.μIoo01, gN] using
    SpherePacking.Integration.DifferentiationUnderIntegral.hasDerivAt_integral_gN_Ioo
      (coeff := coeff) (hf := hf)
      continuousOn_hf continuous_coeff exists_bound_norm_hf coeff_norm_le n x₀

private lemma I_zero_eq_J₁' : (fun x : ℝ => I 0 x) = J₁' := by
  funext x
  simp [RealIntegrals.J₁', I, μ, SpherePacking.Integration.μIoo01, gN, hf, coeff,
    SpherePacking.Integration.DifferentiationUnderIntegral.g,
    SpherePacking.Integration.DifferentiationUnderIntegral.gN, mul_assoc, mul_left_comm, mul_comm,
    intervalIntegral_eq_integral_uIoc, zero_le_one, uIoc_of_le, integral_Ioc_eq_integral_Ioo]

/-- Smoothness of `J₁'` (the primed radial profile). -/
public theorem contDiff_J₁' : ContDiff ℝ (⊤ : ℕ∞) J₁' := by
  simpa [I_zero_eq_J₁'] using SpherePacking.ForMathlib.contDiff_of_hasDerivAt_succ (I := I)
    (fun n x => by simpa using hasDerivAt_integral_gN (n := n) (x₀ := x))

/-- Schwartz-type decay bounds for `J₁'` and its iterated derivatives on `0 ≤ x`. -/
public theorem decay_J₁' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₁' x‖ ≤ C := by
  intro k n
  obtain ⟨B, hB⟩ :=
    SpherePacking.ForMathlib.exists_bound_pow_mul_exp_neg_mul_sqrt k (b := 2*π) (by positivity)
  obtain ⟨Cψ, hCψ⟩ :=
    MagicFunction.b.PsiBounds.PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one
  have hCψ0 : 0 ≤ Cψ :=
    SpherePacking.ForMathlib.nonneg_of_nonneg_le_mul (a := ‖ψS.resToImagAxis 1‖)
      (b := Real.exp (-Real.pi * (1 : ℝ))) (C := Cψ) (norm_nonneg _) (by positivity)
      (by simpa using hCψ 1 le_rfl)
  let bound : ℝ → ℝ := fun t ↦ ((2 * Real.pi) ^ n) * Cψ * t ^ 2
  have hbound_int : Integrable bound μ := by
    simpa [bound, μ, SpherePacking.Integration.μIoo01, mul_assoc, mul_left_comm, mul_comm] using
      (SpherePacking.Integration.integrable_const_mul_pow_muIoo01
        (((2 * Real.pi) ^ n) * Cψ) 2 (by positivity [hCψ0]))
  let Kn : ℝ := ∫ t, bound t ∂μ
  have hKn_nonneg : 0 ≤ Kn := by
    refine integral_nonneg_of_ae <| ?_
    filter_upwards [show ∀ᵐ t ∂μ, t ∈ Ioo (0 : ℝ) 1 by
      simpa [μ] using SpherePacking.Integration.ae_mem_Ioo01_muIoo01] with t ht
    exact mul_nonneg (by positivity [hCψ0]) (pow_nonneg ht.1.le _)
  refine ⟨Kn * B, fun x hx => ?_⟩
  have hIn : ‖I n x‖ ≤ Kn * Real.exp (-2 * Real.pi * Real.sqrt x) := by
    have hbound_ae :
        ∀ᵐ t ∂μ, ‖gN n x t‖ ≤ bound t * Real.exp (-2 * Real.pi * Real.sqrt x) := by
      filter_upwards [show ∀ᵐ t ∂μ, t ∈ Ioo (0 : ℝ) 1 by
        simpa [μ] using SpherePacking.Integration.ae_mem_Ioo01_muIoo01] with t ht
      have hcexp : ‖cexp ((x : ℂ) * coeff t)‖ = Real.exp (-Real.pi * x * t) := by
        simpa using
          SpherePacking.Integration.DifferentiationUnderIntegral.norm_cexp_ofReal_mul_coeff_of_coeff_re
            (coeff := coeff) (x := x) (t := t)
          (show (coeff t).re = -Real.pi * t by
            simp [coeff, Complex.mul_re, show (z₁' t).im = t from by
              simp [show z₁' t = (-1 : ℂ) + (Complex.I : ℂ) * (t : ℂ) from by
                simpa [mul_assoc, mul_left_comm, mul_comm] using
                  z₁'_eq_of_mem (t := t) (mem_Icc_of_Ioo ht)], mul_assoc])
      exact le_mul_of_le_mul_of_nonneg_left
        (by simpa [gN, hf, bound, mul_assoc, mul_left_comm, mul_comm] using
            SpherePacking.Integration.DifferentiationUnderIntegral.norm_gN_le_bound_mul_exp
              (coeff := coeff) (ψ := ψT')
              (z := z₁') (n := n) (Cψ := Cψ) (x := x) (t := t) hCψ0
              (pow_le_pow_left₀ (norm_nonneg _) (coeff_norm_le t) n)
              (by simpa using
                (MagicFunction.norm_modular_rewrite_Ioc_exp_bound (k := 2) (Cψ := Cψ) (ψS := ψS)
                  (ψZ := ψT') (z := z₁') (hCψ := hCψ) (hEq := ψT'_z₁'_eq) (t := t)
                  ⟨ht.1, le_of_lt ht.2⟩))
              hcexp :
          ‖gN n x t‖ ≤ bound t * (Real.exp (-Real.pi * (1 / t)) * Real.exp (-Real.pi * x * t)))
        (by simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          SpherePacking.ForMathlib.exp_neg_pi_div_mul_exp_neg_pi_mul_le (x := x) (t := t) hx ht.1 :
          Real.exp (-Real.pi * (1 / t)) * Real.exp (-Real.pi * x * t) ≤
            Real.exp (-2 * Real.pi * Real.sqrt x))
        (by positivity [hCψ0])
    simpa [I, Kn] using
      (SpherePacking.Integration.DifferentiationUnderIntegral.norm_integral_le_integral_bound_mul_const
        (μ := μ) (f := gN n x) (bound := bound)
        (E := Real.exp (-2 * Real.pi * Real.sqrt x)) (hbound_int := hbound_int) hbound_ae)
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₁' x‖
      = x ^ k * ‖I n x‖ := by
        simp [Real.norm_eq_abs, abs_of_nonneg hx, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
          congrArg (fun F : ℝ → ℂ => F x) (show iteratedDeriv n J₁' = fun x : ℝ ↦ I n x by
            simpa [I_zero_eq_J₁'] using SpherePacking.ForMathlib.iteratedDeriv_eq_of_hasDerivAt_succ
              (I := I) (hI := fun n x => hasDerivAt_integral_gN (n := n) (x₀ := x)) n)]
    _ ≤ x ^ k * (Kn * Real.exp (-2 * Real.pi * Real.sqrt x)) := by gcongr
    _ = Kn * (x ^ k * Real.exp (-2 * Real.pi * Real.sqrt x)) := by ring
    _ ≤ Kn * B := mul_le_mul_of_nonneg_left (by simpa [mul_assoc] using hB x hx) hKn_nonneg

end

end MagicFunction.b.Schwartz.J1Smooth
