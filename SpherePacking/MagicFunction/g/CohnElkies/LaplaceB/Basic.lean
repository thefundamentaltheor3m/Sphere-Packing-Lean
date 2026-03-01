module
import SpherePacking.MagicFunction.g.CohnElkies.Defs
import SpherePacking.MagicFunction.g.CohnElkies.IntegralPieces
import SpherePacking.MagicFunction.g.CohnElkies.LaplaceLemmas
import SpherePacking.MagicFunction.g.CohnElkies.IntegralReductions
import SpherePacking.MagicFunction.g.CohnElkies.DeltaBounds
public import SpherePacking.MagicFunction.b.psi
import SpherePacking.MagicFunction.b.PsiBounds
import SpherePacking.MagicFunction.b.Schwartz.PsiExpBounds.PsiSDecay
import Mathlib.MeasureTheory.Integral.ExpDecay


/-!
# Laplace integral for `b'`

This file defines the Laplace integrand `bLaplaceIntegrand` and proves its convergence on
`(0, ∞)` for `u > 2`.

These lemmas are used in the blueprint proposition `prop:b-double-zeros` (the main statement is
`bRadial_eq_laplace_psiI_main`).

## Main definitions
* `MagicFunction.g.CohnElkies.IntegralReps.bLaplaceIntegrand`

## Main statements
* `MagicFunction.g.CohnElkies.IntegralReps.bLaplaceIntegral_convergent`
-/


namespace MagicFunction.g.CohnElkies.IntegralReps

noncomputable section

open scoped BigOperators Topology UpperHalfPlane
open MeasureTheory Real Complex Filter
open UpperHalfPlane
open MagicFunction.FourierEigenfunctions

/-- The Laplace integrand appearing in the representation of the radial profile `b'`. -/
@[expose] public def bLaplaceIntegrand (u t : ℝ) : ℂ :=
  ψI' ((Complex.I : ℂ) * (t : ℂ)) * Real.exp (-π * u * t)

lemma ψI_apply_eq_factor (z : ℍ) :
    ψI z =
      (1 / 2 : ℂ) *
        (H₄ z ^ (3 : ℕ) *
          (2 * H₄ z ^ (2 : ℕ) + 5 * H₄ z * H₂ z + 5 * H₂ z ^ (2 : ℕ))) / (Δ z) := by
  have hJ : H₃ z = H₂ z + H₄ z := by
    simpa using congrArg (fun f : ℍ → ℂ => f z) (jacobi_identity.symm)
  have hψI0 :
      ψI z =
        (128 : ℂ) * ((H₃ z + H₄ z) / (H₂ z) ^ (2 : ℕ)) +
          (128 : ℂ) * ((H₄ z - H₂ z) / (H₃ z) ^ (2 : ℕ)) := by
    have h := congrArg (fun f : ℍ → ℂ => f z) ψI_eq
    simpa [Pi.smul_apply, nsmul_eq_mul] using h
  have hΔ :
      (Δ z : ℂ) = ((H₂ z) * (H₃ z) * (H₄ z)) ^ 2 / (256 : ℂ) := by
    simpa [Delta_apply] using (Delta_eq_H₂_H₃_H₄ z)
  have hmul :
      ψI z * (Δ z) =
        (1 / 2 : ℂ) *
          (H₄ z ^ (3 : ℕ) *
            (2 * H₄ z ^ (2 : ℕ) + 5 * H₄ z * H₂ z + 5 * H₂ z ^ (2 : ℕ))) := by
    rw [hψI0, hΔ]
    field_simp [H₂_ne_zero z, H₃_ne_zero z, H₄_ne_zero z]
    simp [hJ]
    ring
  have hΔ0 : (Δ z : ℂ) ≠ 0 := by simpa [Delta_apply] using (Δ_ne_zero z)
  exact eq_div_of_mul_eq hΔ0 hmul

/-- Exponential growth bound for `ψI` on vertical rays in the upper half-plane. -/
public lemma exists_ψI_bound_exp :
    ∃ C A : ℝ, 0 < C ∧ ∀ z : ℍ, A ≤ z.im → ‖ψI z‖ ≤ C * Real.exp (2 * π * z.im) := by
  let num : ℍ → ℂ :=
    fun z : ℍ =>
      (1 / 2 : ℂ) *
        (H₄ z ^ (3 : ℕ) *
          (2 * H₄ z ^ (2 : ℕ) + 5 * H₄ z * H₂ z + 5 * H₂ z ^ (2 : ℕ)))
  have hH2 : Tendsto H₂ atImInfty (𝓝 (0 : ℂ)) := H₂_tendsto_atImInfty
  have hH4 : Tendsto H₄ atImInfty (𝓝 (1 : ℂ)) := H₄_tendsto_atImInfty
  have hpoly :
      Tendsto
        (fun z : ℍ =>
          (2 : ℂ) * H₄ z ^ (2 : ℕ) + (5 : ℂ) * (H₄ z * H₂ z) + (5 : ℂ) * H₂ z ^ (2 : ℕ))
        atImInfty (𝓝 (2 : ℂ)) := by
    have hH4_2 := hH4.pow 2
    have hH2_2 := hH2.pow 2
    have hH4H2 := hH4.mul hH2
    simpa [mul_add, add_assoc, add_left_comm, add_comm] using
      (tendsto_const_nhds.mul hH4_2).add
        ((tendsto_const_nhds.mul hH4H2).add (tendsto_const_nhds.mul hH2_2))
  have hnum : Tendsto num atImInfty (𝓝 (1 : ℂ)) := by
    have hH4_3 := hH4.pow 3
    have hprod :
        Tendsto
            (fun z : ℍ =>
              H₄ z ^ (3 : ℕ) *
                (2 * H₄ z ^ (2 : ℕ) + 5 * H₄ z * H₂ z + 5 * H₂ z ^ (2 : ℕ)))
            atImInfty (𝓝 ((1 : ℂ) ^ (3 : ℕ) * (2 : ℂ))) := by
      simpa [mul_add, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
        hH4_3.mul hpoly
    have hconst :
        Tendsto (fun _ : ℍ => (1 / 2 : ℂ)) atImInfty (𝓝 (1 / 2 : ℂ)) :=
      tendsto_const_nhds
    have hlim : ((1 / 2 : ℂ) * ((1 : ℂ) ^ (3 : ℕ) * (2 : ℂ))) = (1 : ℂ) := by
      norm_num
    simpa [num, hlim] using (hconst.mul hprod)
  have hEvNum : ∀ᶠ z in atImInfty, ‖num z‖ ≤ (2 : ℝ) := by
    have hball : Metric.ball (1 : ℂ) 1 ∈ (𝓝 (1 : ℂ)) := Metric.ball_mem_nhds _ (by norm_num)
    have hmem : ∀ᶠ z in atImInfty, num z ∈ Metric.ball (1 : ℂ) 1 := hnum.eventually hball
    filter_upwards [hmem] with z hz
    have hdist : dist (num z) (1 : ℂ) < 1 := by
      simpa [Metric.mem_ball] using hz
    have hnorm1 : ‖(1 : ℂ)‖ = (1 : ℝ) := by simp
    have htriangle :
        ‖num z‖ ≤ ‖num z - (1 : ℂ)‖ + ‖(1 : ℂ)‖ := by
      -- Triangle inequality on `num z = (num z - 1) + 1`.
      simpa [sub_add_cancel] using (norm_add_le (num z - (1 : ℂ)) (1 : ℂ))
    have hdist' : ‖num z - (1 : ℂ)‖ < 1 := by
      assumption
    have hlt : ‖num z‖ < (2 : ℝ) := by
      have h1 :
          ‖num z‖ < 1 + 1 :=
        lt_of_le_of_lt htriangle (add_lt_add_of_lt_of_le hdist' (le_of_eq hnorm1))
      nlinarith
    exact le_of_lt hlt
  have hSet : {z : ℍ | ‖num z‖ ≤ (2 : ℝ)} ∈ atImInfty := by
    simpa using hEvNum
  rcases (UpperHalfPlane.atImInfty_mem _).1 hSet with ⟨A0, hA0⟩
  rcases exists_inv_Delta_bound_exp with ⟨CΔ, AΔ, hCΔ, hΔ⟩
  refine ⟨2 * CΔ, max A0 AΔ, by positivity, ?_⟩
  intro z hz
  have hz0 : A0 ≤ z.im := le_trans (le_max_left _ _) hz
  have hzΔ : AΔ ≤ z.im := le_trans (le_max_right _ _) hz
  have hnum_le : ‖num z‖ ≤ (2 : ℝ) := hA0 z hz0
  have hΔ_le : ‖(Δ z)⁻¹‖ ≤ CΔ * Real.exp (2 * π * z.im) := hΔ z hzΔ
  have hfac : ψI z = num z / (Δ z) := by
    simp [num, ψI_apply_eq_factor]
  calc
    ‖ψI z‖ = ‖num z / (Δ z)‖ := by simp [hfac]
    _ = ‖num z * (Δ z)⁻¹‖ := by simp [div_eq_mul_inv]
    _ = ‖num z‖ * ‖(Δ z)⁻¹‖ := by simp
    _ ≤ (2 : ℝ) * (CΔ * Real.exp (2 * π * z.im)) := by
          exact mul_le_mul hnum_le hΔ_le (by positivity) (by positivity)
    _ = (2 * CΔ) * Real.exp (2 * π * z.im) := by ring

/-- Convergence of the Laplace integral defining `b'` (integrability on `(0, ∞)` for `u > 2`). -/
public lemma bLaplaceIntegral_convergent {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => bLaplaceIntegrand u t) (Set.Ioi (0 : ℝ)) := by
  have hu0 : 0 ≤ u := le_trans (by linarith) (le_of_lt hu)
  have hψI' (t : ℝ) (ht : 0 < t) :
      ψI' ((Complex.I : ℂ) * (t : ℂ)) = ψI.resToImagAxis t := by
    simp [ψI', Function.resToImagAxis, ResToImagAxis, ht]
  have hSlashS (t : ℝ) (ht : 0 < t) :
      ψI.resToImagAxis t = (-(t ^ (2 : ℕ)) : ℂ) * ψS.resToImagAxis (1 / t) := by
    have h :=
      ResToImagAxis.SlashActionS (F := ψS) (k := (-2 : ℤ)) (t := t) ht
    have h' :
        ψI.resToImagAxis t =
          (Complex.I : ℂ) ^ (2 : ℤ) * t ^ (2 : ℤ) * ψS.resToImagAxis (1 / t) := by
      simpa [ψS_slash_S] using h
    calc
      ψI.resToImagAxis t =
          (Complex.I : ℂ) ^ (2 : ℤ) * t ^ (2 : ℤ) * ψS.resToImagAxis (1 / t) := h'
      _ = (-(t ^ (2 : ℕ)) : ℂ) * ψS.resToImagAxis (1 / t) := by
          -- Expand the `zpow` factors and use `I * I = -1`.
          simp [zpow_two, pow_two]
  rcases
      MagicFunction.b.PsiBounds.PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one with
    ⟨Cψ, hCψ⟩
  let Cψ0 : ℝ := max Cψ 0
  have hCψ0 : 0 ≤ Cψ0 := le_max_right _ _
  have hψS_bound (s : ℝ) (hs : 1 ≤ s) :
      ‖ψS.resToImagAxis s‖ ≤ Cψ0 * Real.exp (-π * s) := by
    have hs0 : 0 ≤ Real.exp (-π * s) := by positivity
    have hle : Cψ ≤ Cψ0 := le_max_left _ _
    exact (hCψ s hs).trans (mul_le_mul_of_nonneg_right hle hs0)
  have hcontIoi : ContinuousOn (fun t : ℝ => bLaplaceIntegrand u t) (Set.Ioi (0 : ℝ)) := by
    intro t ht
    have ht0 : 0 < t := ht
    have hEq :
        (fun s : ℝ => bLaplaceIntegrand u s) =ᶠ[𝓝 t]
          fun s : ℝ =>
            (ψI (UpperHalfPlane.ofComplex ((Complex.I : ℂ) * (s : ℂ)))) *
              (Real.exp (-π * u * s) : ℂ) := by
      filter_upwards [lt_mem_nhds ht0] with s hs
      have hsIm : 0 < (((Complex.I : ℂ) * (s : ℂ) : ℂ)).im := by simpa using hs
      simp [bLaplaceIntegrand, ψI', UpperHalfPlane.ofComplex_apply_of_im_pos hsIm, hs]
    have hIm : 0 < (((Complex.I : ℂ) * (t : ℂ) : ℂ)).im := by simpa using ht0
    have hmulI : ContinuousAt (fun s : ℝ => (Complex.I : ℂ) * (s : ℂ)) t := by fun_prop
    have hof : ContinuousAt UpperHalfPlane.ofComplex ((Complex.I : ℂ) * (t : ℂ)) :=
      (UpperHalfPlane.contMDiffAt_ofComplex (n := ⊤) hIm).continuousAt
    have hof' :
        ContinuousAt (fun s : ℝ => UpperHalfPlane.ofComplex ((Complex.I : ℂ) * (s : ℂ))) t :=
      ContinuousAt.comp hof hmulI
    have hψIat : ContinuousAt ψI (UpperHalfPlane.ofComplex ((Complex.I : ℂ) * (t : ℂ))) :=
      (MagicFunction.b.PsiBounds.continuous_ψI).continuousAt
    have hψIcomp :
        ContinuousAt
          (fun s : ℝ => ψI (UpperHalfPlane.ofComplex ((Complex.I : ℂ) * (s : ℂ)))) t :=
      ContinuousAt.comp hψIat hof'
    have hexp : ContinuousAt (fun s : ℝ => (Real.exp (-π * u * s) : ℂ)) t := by fun_prop
    have hmul : ContinuousAt
        (fun s : ℝ =>
          (ψI (UpperHalfPlane.ofComplex ((Complex.I : ℂ) * (s : ℂ)))) *
            (Real.exp (-π * u * s) : ℂ)) t := by
      simpa [mul_assoc] using hψIcomp.mul hexp
    exact (hmul.congr_of_eventuallyEq hEq).continuousWithinAt
  have hint_small :
      IntegrableOn (fun t : ℝ => bLaplaceIntegrand u t) (Set.Ioc (0 : ℝ) 1) := by
    have hmeas :
        AEStronglyMeasurable (fun t : ℝ => bLaplaceIntegrand u t)
          (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      refine (hcontIoi.mono ?_).aestronglyMeasurable measurableSet_Ioc
      intro t ht
      exact ht.1
    have hbound :
        ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), ‖bLaplaceIntegrand u t‖ ≤ Cψ0 := by
      refine ae_restrict_of_forall_mem measurableSet_Ioc ?_
      intro t ht
      have ht0 : 0 < t := ht.1
      have ht1 : t ≤ 1 := ht.2
      have ht' : 1 ≤ (1 / t : ℝ) := by
        have := (one_le_div (show 0 < t from ht0)).2 ht1
        simpa [one_div] using this
      have hψS : ‖ψS.resToImagAxis (1 / t : ℝ)‖ ≤ Cψ0 * Real.exp (-π * (1 / t : ℝ)) :=
        hψS_bound (1 / t : ℝ) ht'
      have hexp_le : Real.exp (-π * (1 / t : ℝ)) ≤ 1 := by
        have hle : (-π * (1 / t : ℝ)) ≤ 0 := by
          have : 0 ≤ (1 / t : ℝ) := le_of_lt (one_div_pos.2 ht0)
          nlinarith [Real.pi_pos, this]
        simpa using (Real.exp_le_one_iff.2 hle)
      have hψS' : ‖ψS.resToImagAxis (1 / t : ℝ)‖ ≤ Cψ0 := by
        have : Cψ0 * Real.exp (-π * (1 / t : ℝ)) ≤ Cψ0 * (1 : ℝ) :=
          mul_le_mul_of_nonneg_left hexp_le hCψ0
        simpa using (hψS.trans this)
      have ht2le : t ^ (2 : ℕ) ≤ 1 := by
        have ht0' : 0 ≤ t := le_of_lt ht0
        simpa using (pow_le_one₀ (n := 2) ht0' ht1)
      have hψI :
          ‖ψI' ((Complex.I : ℂ) * (t : ℂ))‖ ≤ Cψ0 := by
        have hres : ψI' ((Complex.I : ℂ) * (t : ℂ)) = ψI.resToImagAxis t := hψI' t ht0
        rw [hres, hSlashS t ht0]
        have ht2 : 0 ≤ t ^ (2 : ℕ) := by positivity
        have hcoeff : ‖(-(t ^ (2 : ℕ)) : ℂ)‖ = t ^ (2 : ℕ) := by
          simp
        calc
          ‖(-(t ^ (2 : ℕ)) : ℂ) * ψS.resToImagAxis (1 / t)‖
              = ‖(-(t ^ (2 : ℕ)) : ℂ)‖ * ‖ψS.resToImagAxis (1 / t)‖ := by
                  simp
          _ ≤ (t ^ (2 : ℕ)) * Cψ0 := by
                nlinarith [hcoeff, hψS']
          _ ≤ Cψ0 := by
                nlinarith [ht2le]
      have hexp_norm : ‖(Real.exp (-π * u * t) : ℂ)‖ ≤ 1 := by
        have hπ : (-π : ℝ) ≤ 0 := by nlinarith [Real.pi_pos]
        have hut : 0 ≤ u * t := mul_nonneg hu0 (le_of_lt ht0)
        have hle : (-π) * (u * t) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hπ hut
        have hle' : (-π * u * t) ≤ 0 := by simpa [mul_assoc] using hle
        have hExp : Real.exp (-π * u * t) ≤ 1 := Real.exp_le_one_iff.2 hle'
        have hnorm : ‖(Real.exp (-π * u * t) : ℂ)‖ = Real.exp (-π * u * t) := by
          simpa [Complex.ofReal_exp] using (Complex.norm_exp_ofReal (-π * u * t))
        -- Rewrite the complex norm back to the real exponential.
        rw [hnorm]
        exact hExp
      have hnorm :
          ‖bLaplaceIntegrand u t‖ =
            ‖ψI' ((Complex.I : ℂ) * (t : ℂ))‖ * ‖(Real.exp (-π * u * t) : ℂ)‖ := by
        simp [bLaplaceIntegrand]
      rw [hnorm]
      have hmul :
          ‖ψI' ((Complex.I : ℂ) * (t : ℂ))‖ * ‖(Real.exp (-π * u * t) : ℂ)‖ ≤
            ‖ψI' ((Complex.I : ℂ) * (t : ℂ))‖ := by
        simpa using (mul_le_mul_of_nonneg_left hexp_norm (norm_nonneg _))
      exact hmul.trans hψI
    have hs_finite_lt : (volume : Measure ℝ) (Set.Ioc (0 : ℝ) 1) < (⊤ : ENNReal) :=
      (measure_Ioc_lt_top (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ)))
    exact IntegrableOn.of_bound hs_finite_lt hmeas Cψ0 hbound
  rcases exists_ψI_bound_exp with ⟨CI, AI, hCI, hI⟩
  let A : ℝ := max AI 1
  have hint_mid :
      IntegrableOn (fun t : ℝ => bLaplaceIntegrand u t) (Set.Ioc (1 : ℝ) A) := by
    have hcontIcc : ContinuousOn (fun t : ℝ => bLaplaceIntegrand u t) (Set.Icc (1 : ℝ) A) := by
      refine hcontIoi.mono ?_
      intro t ht
      exact lt_of_lt_of_le (by norm_num) ht.1
    have hintIcc :
        IntegrableOn (fun t : ℝ => bLaplaceIntegrand u t) (Set.Icc (1 : ℝ) A)
          (volume : Measure ℝ) :=
      hcontIcc.integrableOn_Icc
    exact hintIcc.mono_set Set.Ioc_subset_Icc_self
  have hint_tail :
      IntegrableOn (fun t : ℝ => bLaplaceIntegrand u t) (Set.Ioi A) := by
    have hmeas :
        AEStronglyMeasurable (fun t : ℝ => bLaplaceIntegrand u t)
          (volume.restrict (Set.Ioi A)) := by
      refine (hcontIoi.mono ?_).aestronglyMeasurable measurableSet_Ioi
      intro t ht
      have hA0 : (0 : ℝ) < A := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
      exact lt_trans hA0 ht
    have hdom :
        ∀ᵐ t ∂(volume.restrict (Set.Ioi A)),
          ‖bLaplaceIntegrand u t‖ ≤ ‖(CI : ℂ) * (Real.exp (-(π * (u - 2)) * t) : ℂ)‖ := by
      refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro t ht
      have htA : A ≤ t := le_of_lt ht
      have htAI : AI ≤ t := le_trans (le_max_left _ _) htA
      have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) htA)
      have htIm : 0 < (((Complex.I : ℂ) * (t : ℂ) : ℂ)).im := by simpa using ht0
      let z : ℍ := ⟨(Complex.I : ℂ) * (t : ℂ), htIm⟩
      have hzIm : AI ≤ z.im := by simpa [z, UpperHalfPlane.im] using htAI
      have hψI : ‖ψI z‖ ≤ CI * Real.exp (2 * π * z.im) := hI z hzIm
      have hψI' : ‖ψI' ((Complex.I : ℂ) * (t : ℂ))‖ ≤ CI * Real.exp (2 * π * t) := by
        have hval : ψI' ((Complex.I : ℂ) * (t : ℂ)) = ψI z := by
          have hz' :
              (⟨(Complex.I : ℂ) * (t : ℂ), by simpa using ht0⟩ : ℍ) = z := by
            ext
            rfl
          simp [ψI', ht0, hz']
        have hψI'0 : ‖ψI z‖ ≤ CI * Real.exp (2 * π * t) := by
          simpa [z, UpperHalfPlane.im] using hψI
        simpa [hval] using hψI'0
      have hcomb :
          Real.exp (2 * π * t) * Real.exp (-π * u * t) =
            Real.exp (-(π * (u - 2)) * t) := by
        have hlin : (2 * π * t) + (-π * u * t) = (-(π * (u - 2)) * t) := by ring_nf
        calc
          Real.exp (2 * π * t) * Real.exp (-π * u * t) =
              Real.exp ((2 * π * t) + (-π * u * t)) := by
                simpa using (Real.exp_add (2 * π * t) (-π * u * t)).symm
          _ = Real.exp (-(π * (u - 2)) * t) := congrArg Real.exp hlin
      have hnorm :
          ‖bLaplaceIntegrand u t‖ =
            ‖ψI' ((Complex.I : ℂ) * (t : ℂ))‖ * ‖(Real.exp (-π * u * t) : ℂ)‖ := by
        simp [bLaplaceIntegrand]
      rw [hnorm]
      have hexp_norm : ‖(Real.exp (-π * u * t) : ℂ)‖ = Real.exp (-π * u * t) := by
        simpa [Complex.ofReal_exp] using (Complex.norm_exp_ofReal (-π * u * t))
      rw [hexp_norm]
      have hpos : 0 ≤ Real.exp (-π * u * t) := le_of_lt (Real.exp_pos _)
      have hmul :
          ‖ψI' ((Complex.I : ℂ) * (t : ℂ))‖ * Real.exp (-π * u * t)
            ≤ (CI * Real.exp (2 * π * t)) * Real.exp (-π * u * t) :=
        mul_le_mul_of_nonneg_right hψI' hpos
      calc
        ‖ψI' ((Complex.I : ℂ) * (t : ℂ))‖ * Real.exp (-π * u * t)
            ≤ (CI * Real.exp (2 * π * t)) * Real.exp (-π * u * t) := hmul
        _ = ‖(CI : ℂ) * (Real.exp (-(π * (u - 2)) * t) : ℂ)‖ := by
              have hnormCI : ‖(CI : ℂ)‖ = CI := by
                simp [abs_of_nonneg (le_of_lt hCI)]
              have hnormExp :
                  ‖(Real.exp (-(π * (u - 2)) * t) : ℂ)‖ = Real.exp (-(π * (u - 2)) * t) := by
                simpa [Complex.ofReal_exp] using
                  (Complex.norm_exp_ofReal (-(π * (u - 2)) * t))
              have hnormProd :
                  ‖(CI : ℂ) * (Real.exp (-(π * (u - 2)) * t) : ℂ)‖ =
                    CI * Real.exp (-(π * (u - 2)) * t) := by
                calc
                  ‖(CI : ℂ) * (Real.exp (-(π * (u - 2)) * t) : ℂ)‖ =
                      ‖(CI : ℂ)‖ * ‖(Real.exp (-(π * (u - 2)) * t) : ℂ)‖ := by
                        simp
                  _ = CI * Real.exp (-(π * (u - 2)) * t) := by
                        rw [hnormCI, hnormExp]
              have hstep :
                  (CI * Real.exp (2 * π * t)) * Real.exp (-π * u * t) =
                    CI * Real.exp (-(π * (u - 2)) * t) := by
                calc
                  (CI * Real.exp (2 * π * t)) * Real.exp (-π * u * t) =
                      CI * (Real.exp (2 * π * t) * Real.exp (-π * u * t)) := by
                        simp [mul_assoc]
                  _ = CI * Real.exp (-(π * (u - 2)) * t) := by
                        simpa [mul_assoc] using congrArg (fun x : ℝ => CI * x) hcomb
              -- Turn the real product into a complex norm.
              rw [hstep]
              exact hnormProd.symm
    have hpos : 0 < π * (u - 2) := by
      have : 0 < u - 2 := sub_pos.2 hu
      exact mul_pos Real.pi_pos this
    have hExp :
        IntegrableOn (fun t : ℝ => Real.exp (-(π * (u - 2)) * t)) (Set.Ioi A) := by
      simpa [mul_assoc] using (exp_neg_integrableOn_Ioi (a := A) (b := π * (u - 2)) hpos)
    have hExpC :
        IntegrableOn (fun t : ℝ => (CI : ℂ) * (Real.exp (-(π * (u - 2)) * t) : ℂ)) (Set.Ioi A) := by
      have hE :
          Integrable (fun t : ℝ => Real.exp (-(π * (u - 2)) * t))
            (volume.restrict (Set.Ioi A)) := by
        simpa [IntegrableOn] using hExp
      have hE' :
          Integrable (fun t : ℝ => (Real.exp (-(π * (u - 2)) * t) : ℂ))
            (volume.restrict (Set.Ioi A)) :=
        hE.ofReal
      simpa [IntegrableOn] using hE'.const_mul (CI : ℂ)
    exact
      (MeasureTheory.Integrable.mono (μ := volume.restrict (Set.Ioi A))
        (by simpa [IntegrableOn] using hExpC) hmeas hdom)
  have hUnion1 : Set.Ioi (1 : ℝ) = Set.Ioc (1 : ℝ) A ∪ Set.Ioi A := by
    ext t
    constructor
    · intro ht
      by_cases htA : t ≤ A
      · exact Or.inl ⟨ht, htA⟩
      · exact Or.inr (lt_of_not_ge htA)
    · intro ht
      rcases ht with ht | ht
      · exact ht.1
      · have h1A : (1 : ℝ) ≤ A := by
          simp [A]
        exact lt_of_le_of_lt h1A ht
  have hint_large :
      IntegrableOn (fun t : ℝ => bLaplaceIntegrand u t) (Set.Ioi (1 : ℝ)) := by
    simpa [hUnion1] using (hint_mid.union hint_tail)
  have hUnion0 :
      Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
    norm_num
  have h := hint_small.union hint_large
  -- Rewrite the domain of integration using the set identity.
  rw [hUnion0]
  exact h

end

end MagicFunction.g.CohnElkies.IntegralReps
