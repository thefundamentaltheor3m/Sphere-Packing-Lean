module
public import SpherePacking.ModularForms.Derivative.Equivariance

@[expose] public section

/-!
# Monotonicity criterion on the imaginary axis (`antiSerreDerPos`)

This file collects results about the interaction of the (Serre) derivative with restriction to
the imaginary axis: the chain rule `d/dt F(it) = -2π · (D F)(it)`, small real-part helpers, and
the main monotonicity criterion `antiSerreDerPos`: if `F : ℍ → ℂ` is holomorphic, takes real
values on the imaginary axis, the Serre derivative `serre_D k F` is positive on that axis, and
`F(it)` is positive for large `t`, then `F(it)` is positive for all `t > 0`.

The companion logarithmic-derivative identity `D Δ = E₂ · Δ` is also proved here since it is
needed by the monotonicity argument.
-/

open scoped ModularForm MatrixGroups Manifold Topology BigOperators

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap ModularForm
open ModularFormClass
open Metric Filter Function

/-
Interaction between (Serre) derivative and restriction to the imaginary axis.
-/
lemma StrictAntiOn.eventuallyPos_Ioi {g : ℝ → ℝ} (hAnti : StrictAntiOn g (Set.Ioi (0 : ℝ)))
    {t₀ : ℝ} (ht₀_pos : 0 < t₀) (hEv : ∀ t : ℝ, t₀ ≤ t → 0 < g t) :
    ∀ t : ℝ, 0 < t → 0 < g t := by
  intro t ht
  by_cases hcase : t₀ ≤ t
  · exact hEv t hcase
  · exact (hEv t₀ le_rfl).trans (hAnti ht ht₀_pos (lt_of_not_ge hcase))

/--
Chain rule on the imaginary axis: `d/dt F(it) = -2π * (D F)(it)`.
Equivalently, `deriv F.resToImagAxis t = -2π * (D F).resToImagAxis t`.
-/
public theorem deriv_resToImagAxis_eq (F : ℍ → ℂ) (hF : MDiff F) {t : ℝ} (ht : 0 < t) :
    deriv F.resToImagAxis t = -2 * π * (D F).resToImagAxis t := by
  let z : ℍ := ⟨I * t, by simp [ht]⟩
  let g : ℝ → ℂ := (I * ·)
  have h_eq : F.resToImagAxis =ᶠ[nhds t] ((F ∘ ofComplex) ∘ g) := by
    filter_upwards [lt_mem_nhds ht] with s hs
    have him : 0 < (g s).im := by simp [g, hs]
    simp [Function.resToImagAxis_apply, ResToImagAxis, hs, Function.comp_apply, g,
      ofComplex_apply_of_im_pos him]
  rw [h_eq.deriv_eq]
  have hg : HasDerivAt g I t := by simpa using ofRealCLM.hasDerivAt.const_mul I
  have hF' := (MDifferentiableAt_DifferentiableAt (hF z)).hasDerivAt
  rw [(hF'.scomp t hg).deriv]
  have hD : deriv (F ∘ ofComplex) z = 2 * π * I * D F z := by simp only [D]; field_simp
  simp only [hD, Function.resToImagAxis_apply, ResToImagAxis, dif_pos ht, z, smul_eq_mul]
  ring_nf
  simp only [I_sq]
  ring

/-- The real part of F.resToImagAxis has derivative -2π * ((D F).resToImagAxis t).re at t. -/
lemma hasDerivAt_resToImagAxis_re {F : ℍ → ℂ} (hdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => (F.resToImagAxis s).re) (-2 * π * ((D F).resToImagAxis t).re) t := by
  have hdiffAt := ResToImagAxis.Differentiable F hdiff t ht
  have hderivC := hdiffAt.hasDerivAt.congr_deriv (deriv_resToImagAxis_eq F hdiff ht)
  simpa using (hasDerivAt_const t (Complex.reCLM : ℂ →L[ℝ] ℝ)).clm_apply hderivC

public theorem hasDerivAt_re_resToImagAxis (F : ℍ → ℂ) (hF : MDiff F) :
    ∀ t,
      0 < t →
        HasDerivAt (fun t => (F.resToImagAxis t).re) (-2 * π * (ResToImagAxis (D F) t).re) t :=
  fun t ht => by
    have hdiff : DifferentiableAt ℝ F.resToImagAxis t := ResToImagAxis.Differentiable F hF t ht
    have hderivC : HasDerivAt F.resToImagAxis (-2 * π * (D F).resToImagAxis t) t :=
      hdiff.hasDerivAt.congr_deriv (deriv_resToImagAxis_eq F hF ht)
    simpa using
      (hasDerivAt_const (x := t) (c := (Complex.reCLM : ℂ →L[ℝ] ℝ))).clm_apply hderivC

public lemma mul_re_of_im_eq_zero {x y : ℂ} (hx : x.im = 0) (hy : y.im = 0) :
    (x * y).re = x.re * y.re := by
  simp [Complex.mul_re, hx, hy]

/--
Logarithmic derivative of the discriminant: `D Δ = E₂ * Δ` (used in `antiSerreDerPos`).
-/
public theorem D_Delta_eq_E₂_mul_Delta : D Δ = E₂ * Δ := by
  funext z
  have h_eq :
      (fun w : ℂ => Δ (ofComplex w)) =ᶠ[nhds (z : ℂ)] fun w => (η w) ^ (24 : ℕ) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simpa [ofComplex_apply_of_im_pos hw] using (Delta_eq_eta_pow (ofComplex w))
  have hηnz : η (z : ℂ) ≠ 0 := ModularForm.eta_ne_zero z.2
  have hlog :
      logDeriv (fun w : ℂ => (η w) ^ (24 : ℕ)) (z : ℂ) = (2 * π * I) * E₂ z := by
    have hpowdiff : DifferentiableAt ℂ (fun x : ℂ => x ^ (24 : ℕ)) (η (z : ℂ)) := by
      fun_prop
    calc
      logDeriv (fun w : ℂ => (η w) ^ (24 : ℕ)) (z : ℂ) =
          logDeriv (fun x : ℂ => x ^ (24 : ℕ)) (η (z : ℂ)) * deriv η (z : ℂ) := by
            simpa [Function.comp] using
              (logDeriv_comp (x := (z : ℂ)) hpowdiff
                (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet z.2))
      _ = ((24 : ℂ) / η (z : ℂ)) * deriv η (z : ℂ) := by
            simp [logDeriv_pow]
      _ = (24 : ℂ) * logDeriv η (z : ℂ) := by
            simp [logDeriv, div_eq_mul_inv, mul_assoc, mul_comm]
      _ = (2 * π * I) * E₂ z := by
            rw [ModularForm.logDeriv_eta_eq_E2 z, E₂]
            ring
  have hderiv_eta_pow :
      deriv (fun w : ℂ => (η w) ^ (24 : ℕ)) (z : ℂ) =
        (2 * π * I) * E₂ z * (η (z : ℂ) ^ (24 : ℕ)) := by
    have :
        deriv (fun w : ℂ => (η w) ^ (24 : ℕ)) (z : ℂ) =
          logDeriv (fun w : ℂ => (η w) ^ (24 : ℕ)) (z : ℂ) *
            (η (z : ℂ) ^ (24 : ℕ)) := by
      simp [logDeriv, div_mul_eq_mul_div, mul_div_cancel_right₀ _ (pow_ne_zero _ hηnz)]
    simpa [hlog, mul_assoc, mul_left_comm, mul_comm] using this
  have h2piI : (2 * π * I : ℂ) ≠ 0 := two_pi_I_ne_zero
  have hηpow : η (z : ℂ) ^ (24 : ℕ) = Δ z := (Delta_eq_eta_pow z).symm
  calc
    D Δ z = (2 * π * I)⁻¹ * deriv (fun w : ℂ => Δ (ofComplex w)) (z : ℂ) := rfl
    _ = (2 * π * I)⁻¹ * deriv (fun w : ℂ => (η w) ^ (24 : ℕ)) (z : ℂ) := by
          simp [h_eq.deriv_eq]
    _ = (2 * π * I)⁻¹ * ((2 * π * I) * E₂ z * (η (z : ℂ) ^ (24 : ℕ))) := by
          simp [hderiv_eta_pow]
    _ = E₂ z * (η (z : ℂ) ^ (24 : ℕ)) := by
          field_simp [h2piI]
    _ = E₂ z * Δ z := by simp [hηpow]

/--
Let $F : \mathbb{H} \to \mathbb{C}$ be holomorphic with $F(it)$ real for all $t > 0$.
Assume $\partial_k F$ is positive on the imaginary axis and $F(it)$ is positive for large $t$.
Then $F(it)$ is positive for all $t > 0$.
-/
public theorem antiSerreDerPos {F : ℍ → ℂ} {k : ℤ} (hFderiv : MDiff F)
    (hSDF : ResToImagAxis.Pos (serre_D k F)) (hF : ResToImagAxis.EventuallyPos F) :
    ResToImagAxis.Pos F := by
  -- Blueprint proof: integrating factor `Δ(it)^{-k/12}` makes the Serre
  -- derivative into an `D`-derivative.
  have hF_real : ResToImagAxis.Real F := hF.1
  obtain ⟨-, t₀, ht₀_pos, hF_pos⟩ := hF
  have hΔpos : ResToImagAxis.Pos Δ := Delta_imag_axis_pos
  have hΔreal : ResToImagAxis.Real Δ := hΔpos.1
  have hΔre_pos : ∀ t : ℝ, 0 < t → 0 < (Δ.resToImagAxis t).re := hΔpos.2
  let a : ℝ := (((k : ℂ) * 12⁻¹) : ℂ).re
  let g : ℝ → ℝ := fun t => (F.resToImagAxis t).re
  let d : ℝ → ℝ := fun t => (Δ.resToImagAxis t).re
  let h : ℝ → ℝ := fun t => g t * (d t) ^ (-a)
  have hE₂real : ResToImagAxis.Real E₂ := E₂_imag_axis_real
  have hg :
      ∀ t, 0 < t → HasDerivAt g (-2 * π * (ResToImagAxis (D F) t).re) t :=
    fun t ht => by
      simpa [g] using hasDerivAt_re_resToImagAxis F hFderiv t ht
  have hΔholo : MDiff Δ := by
    simpa [Delta_apply] using (Delta.holo' : MDiff Δ)
  have hd :
      ∀ t, 0 < t → HasDerivAt d (-2 * π * (ResToImagAxis (D Δ) t).re) t :=
    fun t ht => by
      simpa [d] using hasDerivAt_re_resToImagAxis Δ hΔholo t ht
  have hh : ∀ t, 0 < t →
      HasDerivAt h
        ((-2 * π * (ResToImagAxis (D F) t).re) * (d t) ^ (-a) +
            (g t) * ((-a) * (d t) ^ (-a - 1) * (-2 * π * (ResToImagAxis (D Δ) t).re))) t :=
    fun t ht => by
      have hdpos : 0 < d t := hΔre_pos t ht
      have hdne : d t ≠ 0 := ne_of_gt hdpos
      have hpow :
          HasDerivAt (fun t => (d t) ^ (-a))
            ((-a) * (d t) ^ (-a - 1) * (-2 * π * (ResToImagAxis (D Δ) t).re)) t := by
        have hpow0 :
            HasDerivAt (fun x : ℝ => x ^ (-a)) ((-a) * (d t) ^ (-a - 1)) (d t) := by
          simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_assoc] using
            (Real.hasDerivAt_rpow_const (x := d t) (p := -a) (Or.inl hdne))
        simpa [mul_assoc, mul_left_comm, mul_comm] using hpow0.comp t (hd t ht)
      have := (hg t ht).mul hpow
      simpa [h, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using this
  have hn : ∀ t ∈ Set.Ioi (0 : ℝ), deriv h t < 0 := fun t (ht : 0 < t) => by
    have hdpos : 0 < d t := hΔre_pos t ht
    have hdpowpos : 0 < (d t) ^ (-a) := Real.rpow_pos_of_pos hdpos (-a)
    have hSpos : 0 < ((serre_D k F).resToImagAxis t).re := hSDF.2 t ht
    have hk_im : ((((k : ℂ) * 12⁻¹) : ℂ).im = 0) := by simp
    have hE₂im : (E₂.resToImagAxis t).im = 0 := hE₂real t ht
    have hFim : (F.resToImagAxis t).im = 0 := hF_real t ht
    have hΔim : (Δ.resToImagAxis t).im = 0 := hΔreal t ht
    have hDΔre : (ResToImagAxis (D Δ) t).re = (E₂.resToImagAxis t).re * d t := by
      simpa [D_Delta_eq_E₂_mul_Delta, ResToImagAxis, Function.resToImagAxis, ht, d] using
        mul_re_of_im_eq_zero (x := E₂.resToImagAxis t) (y := Δ.resToImagAxis t) hE₂im hΔim
    have hSerre_re :
        ((serre_D k F).resToImagAxis t).re =
          (ResToImagAxis (D F) t).re - a * (E₂.resToImagAxis t).re * g t := by
      have hRes :
          (serre_D k F).resToImagAxis t =
            (D F).resToImagAxis t -
              (((k : ℂ) * 12⁻¹) : ℂ) * (E₂.resToImagAxis t * F.resToImagAxis t) := by
        simp [serre_D, Function.resToImagAxis, ResToImagAxis, ht, mul_assoc]
      have h' := congrArg Complex.re hRes
      have houter :
          (((((k : ℂ) * 12⁻¹) : ℂ) * (E₂.resToImagAxis t * F.resToImagAxis t))).re =
            a * (E₂.resToImagAxis t * F.resToImagAxis t).re := by
        rw [Complex.mul_re]
        simp [a, hk_im]
      have hE₂im0 : (ResToImagAxis E₂ t).im = 0 := by
        simpa [Function.resToImagAxis_apply] using hE₂im
      have hFim0 : (ResToImagAxis F t).im = 0 := by
        simpa [Function.resToImagAxis_apply] using hFim
      simpa [a, g, Complex.sub_re, houter,
        mul_re_of_im_eq_zero (x := ResToImagAxis E₂ t) (y := ResToImagAxis F t) hE₂im0 hFim0,
        mul_assoc] using h'
    -- Rewrite `deriv h t` as `(-2π) * (d t)^(-a) * ((serre_D k F)(it)).re`.
    have hderiv :
        deriv h t = (-2 * π) * (d t) ^ (-a) * ((serre_D k F).resToImagAxis t).re := by
      -- Start from the explicit derivative formula provided by `hh`.
      rw [(hh t ht).deriv]
      -- Rewrite the Serre-derivative term.
      rw [hSerre_re]
      have hx : d t ≠ 0 := (ne_of_gt hdpos)
      have hrpow : (d t) ^ (-a - 1) * d t = (d t) ^ (-a) := by
        have h := Real.rpow_add_one (x := d t) hx (-a - 1)
        -- `d^( (-a-1)+1 ) = d^(-a-1) * d`.
        -- Rearranged, this is exactly `d^(-a-1) * d = d^(-a)`.
        simpa [add_assoc, add_left_comm, add_comm] using h.symm
      grind only
    have hneg : (-2 * π : ℝ) < 0 := by nlinarith [Real.pi_pos]
    -- Combine signs.
    rw [hderiv, mul_assoc]
    have hpos : 0 < (d t) ^ (-a) * ((serre_D k F).resToImagAxis t).re := mul_pos hdpowpos hSpos
    exact mul_neg_of_neg_of_pos hneg hpos
  have hAnti : StrictAntiOn h (Set.Ioi (0 : ℝ)) :=
    strictAntiOn_of_deriv_neg (convex_Ioi (0 : ℝ))
      (fun x hx => (hh x hx).continuousAt.continuousWithinAt)
      (by simpa [interior_Ioi] using hn)
  have hEv : ∀ t : ℝ, t₀ ≤ t → 0 < h t := fun t ht => by
    have htpos : 0 < t := lt_of_lt_of_le ht₀_pos ht
    have hgpos : 0 < g t := hF_pos t ht
    have hdpos : 0 < d t := hΔre_pos t htpos
    have hdpowpos : 0 < (d t) ^ (-a) := Real.rpow_pos_of_pos hdpos (-a)
    simpa [h, g, d, mul_assoc] using mul_pos hgpos hdpowpos
  have hall : ∀ t : ℝ, 0 < t → 0 < h t :=
    StrictAntiOn.eventuallyPos_Ioi hAnti ht₀_pos hEv
  refine ⟨hF_real, fun t ht => ?_⟩
  have hdpos : 0 < d t := hΔre_pos t ht
  have hdpowpos : 0 < (d t) ^ (-a) := Real.rpow_pos_of_pos hdpos (-a)
  have : 0 < g t := by
    have htpos : 0 < h t := hall t ht
    exact pos_of_mul_pos_left htpos (le_of_lt hdpowpos)
  simpa [g] using this
