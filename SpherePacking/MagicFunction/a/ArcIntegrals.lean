/-
Copyright (c) 2026 The Sphere Packing Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere Packing Contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import SpherePacking.MagicFunction.PolyFourierCoeffBound
public import SpherePacking.MagicFunction.a.Defs
public import SpherePacking.MagicFunction.a.Integrability.ComplexIntegrands
public import SpherePacking.ModularForms.PhiTransform

/-!
# The Fourier transforms of `I₁`, `I₂` as arc integrals, and a common primitive

The integrals `I₁'` and `I₂'` of `SpherePacking.MagicFunction.a.Defs` are
$$I_1(r) = \int_{-1}^{-1+i} \varphi_0\left(\frac{-1}{z+1}\right) (z+1)^2 e^{\pi i r z}\,dz,
\qquad
I_2(r) = \int_{-1+i}^{i} \varphi_0\left(\frac{-1}{z+1}\right) (z+1)^2 e^{\pi i r z}\,dz,$$
along straight segments, and `I₁ x = I₁' ‖x‖²`, `I₂ x = I₂' ‖x‖²` on `ℝ⁸`.

**Fourier transform.** In dimension 8, the Fourier transform of `x ↦ e^{πi‖x‖² z}` is
`ξ ↦ z⁻⁴ e^{πi‖ξ‖² (-1/z)}`. Hence, with `r = ‖ξ‖²`,
$$\mathcal F I_1(\xi) = \int_{-1}^{-1+i} \varphi_0\left(\frac{-1}{z+1}\right) (z+1)^2 z^{-4}
  e^{-\pi i r / z}\,dz,$$
and similarly for `I₂`.

**Change of variables.** Applying the inversion `S(z) = -1/z`, i.e. substituting `z = -1/w`,
`dz = dw / w²`, we have `z + 1 = (w - 1) / w`, `-1/(z+1) = w / (1 - w)`, `z⁻⁴ = w⁴` and
`e^{-πir/z} = e^{πirw}`, so both integrands become
$$\Psi(w) = \varphi_0\left(\frac{w}{1-w}\right) (1-w)^2 e^{\pi i r w},$$
which equals the integrand `Φ₃' r w = φ₀(-1/(w-1)) (w-1)² e^{πirw}` of `I₃`, `I₄` by
`1`-periodicity of `φ₀`, since `w / (1 - w) = -1/(w - 1) - 1`. The inversion maps
* the segment `[-1, -1 + i]` onto the arc of `|w - 1/2| = 1/2` from `1` to `(1 + i)/2`,
  parametrised by `θ ↦ 1/2 + 1/2 e^{iθ}`, `θ ∈ [0, π/2]`;
* the segment `[-1 + i, i]` onto the arc of `|w - i/2| = 1/2` from `(1 + i)/2` to `i`,
  parametrised by `θ ↦ i/2 + 1/2 e^{iθ}`, `θ ∈ [0, π/2]`.
Hence `𝓕 I₁ ξ = I₁'_arc ‖ξ‖²` and `𝓕 I₂ ξ = I₂'_arc ‖ξ‖²`, where
$$I_1^{arc}(r) = \int_0^{\pi/2} \Psi\left(\tfrac12 + \tfrac12 e^{i\theta}\right)
  \tfrac{i}{2} e^{i\theta}\,d\theta,
\qquad
I_2^{arc}(r) = \int_0^{\pi/2} \Psi\left(\tfrac{i}{2} + \tfrac12 e^{i\theta}\right)
  \tfrac{i}{2} e^{i\theta}\,d\theta.$$
These facts (`fourier_I₁_eq`, `fourier_I₂_eq`) are taken for granted (`sorry`); `Ψ₁'_eq_Φ₃'` is
proved from `φ₀_periodic`.

**A common primitive.** `Φ₃'` is holomorphic on the (convex) upper half plane (`Φ₃'_holo`), so
it has a primitive `F` there (`Convex.exists_forall_hasDerivWithinAt`), which is then also a
primitive of `Ψ₁' = Ψ₂' = Φ₃' = Φ₄'`. By the fundamental theorem of calculus:
* `I₁'_arc_eq_sub_lim`: `I₁'_arc r = F r ((1 + i)/2) - lim_{θ → 0⁺} F r (w₁ θ)`;
* `I₂'_arc_eq_sub`: `I₂'_arc r = F r i - F r ((1 + i)/2)`;
* `I₃'_eq_sub_lim`: `I₃' r = F r (1 + i) - lim_{t → 0⁺} F r (z₃' t)`;
* `I₄'_eq_sub`: `I₄' r = F r i - F r (1 + i)`;
the limits using that the integrand vanishes as the curve approaches `1` (`tendsto_Ψ₁'_w₁`,
`tendsto_Φ₃'_z₃'`, from the bound `‖Φ₃' r z‖ ≤ C ‖z - 1‖²` near `1`, `norm_Φ₃'_le_near_one`).
Therefore `I₁'_arc + I₂'_arc = I₃' + I₄'` (`I₁'_arc_add_I₂'_arc_eq`) reduces to the equality of
the two limits of `F` at `1` along `w₁` and along `z₃'` (`lim_F_w₁_eq_lim_F_z₃'`). To prove it, we
take the two limits independently in `ε₁` and `ε₂`: `F (w₁ ε₁) - F (z₃' ε₂)` is the integral of
`Φ₃'` along the segment joining the two points (`F_sub_eq_integral_segment`). Since `Φ₃'` is
bounded by `M` on a closed disc tangent to the real line at `1` (`Φ₃'_bounded_near_one`, from the
uniform bound `norm_φ₀_le` on `φ₀`), which eventually contains both points and hence the segment,
this is at most `M ‖w₁ ε₁ - z₃' ε₂‖ → 0` (`tendsto_F_w₁_sub_F_z₃'`).

Combined with `fourier_I₁_eq`, `fourier_I₂_eq`, this gives `fourier_I₁_add_fourier_I₂`:
`𝓕 I₁ + 𝓕 I₂ = I₃ + I₄`, used to prove `MagicFunction.a.Fourier.perm_I₁_I₂`.
-/

@[expose] public section

open Set Complex Real

noncomputable section

namespace MagicFunction.a.ArcIntegrals

variable (r : ℝ)

/-- The arc of `|w - 1/2| = 1/2` from `1` (at `θ = 0`) to `(1 + i)/2` (at `θ = π/2`); the image of
the segment `[-1, -1 + i]` under `z ↦ -1/z`. -/
def w₁ (θ : ℝ) : ℂ := circleMap (1 / 2) (1 / 2) θ

/-- The arc of `|w - i/2| = 1/2` from `(1 + i)/2` (at `θ = 0`) to `i` (at `θ = π/2`); the image of
the segment `[-1 + i, i]` under `z ↦ -1/z`. -/
def w₂ (θ : ℝ) : ℂ := circleMap (I / 2) (1 / 2) θ

/-- The complex integrand of the Fourier transform of `I₁`, after the substitution `z = -1/w`. -/
def Ψ₁' : ℂ → ℂ := fun w ↦ φ₀'' (w / (1 - w)) * (1 - w) ^ 2 * cexp (π * I * r * w)

/-- The complex integrand of the Fourier transform of `I₂`, after the substitution `z = -1/w`. -/
def Ψ₂' : ℂ → ℂ := fun w ↦ φ₀'' (w / (1 - w)) * (1 - w) ^ 2 * cexp (π * I * r * w)

/-- The Fourier transform of `I₁` (as a function of `r = ‖ξ‖²`) as an integral over the arc `w₁`.
Note `deriv w₁ θ = circleMap 0 (1/2) θ * I`. -/
def I₁'_arc : ℝ → ℂ := fun x ↦
  ∫ θ in (0 : ℝ)..(π / 2), circleMap 0 (1 / 2) θ * I * Ψ₁' x (w₁ θ)

/-- The Fourier transform of `I₂` (as a function of `r = ‖ξ‖²`) as an integral over the arc `w₂`.
Note `deriv w₂ θ = circleMap 0 (1/2) θ * I`. -/
def I₂'_arc : ℝ → ℂ := fun x ↦
  ∫ θ in (0 : ℝ)..(π / 2), circleMap 0 (1 / 2) θ * I * Ψ₂' x (w₂ θ)

section Sanity

lemma w₁_zero : w₁ 0 = 1 := by
  simp [w₁, circleMap]; norm_num

lemma w₁_pi_div_two : w₁ (π / 2) = (1 + I) / 2 := by
  have : cexp (↑(π / 2) * I) = I := by
    rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]; simp
  simp only [w₁, circleMap, this]; push_cast; ring

lemma w₂_zero : w₂ 0 = (1 + I) / 2 := by
  simp [w₂, circleMap]; ring

lemma w₂_pi_div_two : w₂ (π / 2) = I := by
  have : cexp (↑(π / 2) * I) = I := by
    rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]; simp
  simp only [w₂, circleMap, this]; push_cast; ring

lemma deriv_w₁ (θ : ℝ) : deriv w₁ θ = circleMap 0 (1 / 2) θ * I :=
  deriv_circleMap _ _ _

lemma deriv_w₂ (θ : ℝ) : deriv w₂ θ = circleMap 0 (1 / 2) θ * I :=
  deriv_circleMap _ _ _

end Sanity

section Fourier

open scoped FourierTransform

/-- The Fourier transform of `I₁`, after the change of variables `z = -1/w`, is the arc integral
`I₁'_arc` (of the radius squared). -/
theorem fourier_I₁_eq (ξ : EuclideanSpace ℝ (Fin 8)) :
    𝓕 MagicFunction.a.RadialFunctions.I₁ ξ = I₁'_arc (‖ξ‖ ^ 2) := by
  sorry

/-- The Fourier transform of `I₂`, after the change of variables `z = -1/w`, is the arc integral
`I₂'_arc` (of the radius squared). -/
theorem fourier_I₂_eq (ξ : EuclideanSpace ℝ (Fin 8)) :
    𝓕 MagicFunction.a.RadialFunctions.I₂ ξ = I₂'_arc (‖ξ‖ ^ 2) := by
  sorry

end Fourier

/-! ## A primitive of the integrand on the upper half plane -/

section Primitive

open UpperHalfPlane (upperHalfPlaneSet isOpen_upperHalfPlaneSet)
open Filter Topology MagicFunction.Parametrisations

local notation "ℍₒ" => upperHalfPlaneSet

open MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands
  MagicFunction.a.RealIntegrals

/-- `φ₀''` is `1`-periodic on all of `ℂ` (both sides vanish off the upper half plane). -/
lemma φ₀''_add_one (z : ℂ) : φ₀'' (z + 1) = φ₀'' z := by
  by_cases hz : 0 < z.im
  · have hz' : 0 < (z + 1).im := by simpa using hz
    rw [φ₀''_def hz', φ₀''_def hz, ← φ₀_periodic ⟨z, hz⟩]
    congr 1
    ext
    simp [add_comm]
  · simp [φ₀'', hz]

/-- The integrand of the (transformed) Fourier transform of `I₁` is that of `I₃`. This follows from
the `1`-periodicity of `φ₀`, as `w / (1 - w) = -1/(w - 1) - 1`. -/
lemma Ψ₁'_eq_Φ₃' : Ψ₁' r = Φ₃' r := by
  funext w
  simp only [Ψ₁', Φ₃']
  by_cases hw : w = 1
  · subst hw; simp
  · have h₁ : 1 - w ≠ 0 := sub_ne_zero.2 (Ne.symm hw)
    have h₂ : w - 1 ≠ 0 := sub_ne_zero.2 hw
    have h : -1 / (w - 1) = w / (1 - w) + 1 := by field_simp; ring
    rw [h, φ₀''_add_one]
    ring

/-- The integrand of the (transformed) Fourier transform of `I₂` is that of `I₃`. -/
lemma Ψ₂'_eq_Φ₃' : Ψ₂' r = Φ₃' r :=
  Ψ₁'_eq_Φ₃' r

lemma Φ₄'_eq_Φ₃' : Φ₄' r = Φ₃' r :=
  rfl

/-- The common primitive of `Ψ₁' = Ψ₂' = Φ₃' = Φ₄'` on the (convex) upper half plane. -/
def F : ℂ → ℂ :=
  (Convex.exists_forall_hasDerivWithinAt (convex_halfSpace_im_gt 0) (Φ₃'_holo (r := r))).choose

lemma hasDerivAt_F {z : ℂ} (hz : z ∈ ℍₒ) : HasDerivAt (F r) (Φ₃' r z) z :=
  ((Convex.exists_forall_hasDerivWithinAt (convex_halfSpace_im_gt 0)
    (Φ₃'_holo (r := r))).choose_spec z hz).hasDerivAt (isOpen_upperHalfPlaneSet.mem_nhds hz)

/-! ### General facts: FTC along a curve, and the limit at a boundary endpoint -/

/-- Fundamental theorem of calculus along a `C¹` curve `γ` contained in the upper half plane. -/
lemma integral_curve_eq_sub {f F : ℂ → ℂ} (hf : ContinuousOn f ℍₒ)
    (hF : ∀ z ∈ ℍₒ, HasDerivAt F (f z) z) {γ γ' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ t, HasDerivAt γ (γ' t) t) (hγ' : Continuous γ')
    (hγ : ∀ t ∈ Icc a b, γ t ∈ ℍₒ) :
    ∫ t in a..b, γ' t * f (γ t) = F (γ b) - F (γ a) := by
  have hD : ∀ t ∈ Icc a b, HasDerivAt (fun t ↦ F (γ t)) (γ' t * f (γ t)) t := fun t ht ↦
    ((hF _ (hγ t ht)).comp t (hd t)).congr_deriv (mul_comm _ _)
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (fun t ht ↦ (hD t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ hD t (Ioo_subset_Icc_self ht)) (ContinuousOn.intervalIntegrable ?_)
  rw [uIcc_of_le hab]
  exact fun t ht ↦ (hγ'.continuousAt.mul ((hf.continuousAt
    (isOpen_upperHalfPlaneSet.mem_nhds (hγ t ht))).comp (hd t).continuousAt)).continuousWithinAt

/-- Let `γ` be a `C¹` curve with `γ (0, b] ⊆ ℍ`, and `F` a primitive of `f` on `ℍ`. If
`f (γ t) → 0 = f (γ 0)` as `t → 0⁺`, then `F (γ t) → F (γ b) - ∫₀ᵇ f(γ t) γ'(t) dt` as `t → 0⁺`. -/
theorem tendsto_primitive_curve {f F : ℂ → ℂ} (hf : ContinuousOn f ℍₒ)
    (hF : ∀ z ∈ ℍₒ, HasDerivAt F (f z) z) {γ γ' : ℝ → ℂ} {b : ℝ} (hb : 0 < b)
    (hd : ∀ t, HasDerivAt γ (γ' t) t) (hγ' : Continuous γ')
    (hγ : ∀ t ∈ Ioc 0 b, γ t ∈ ℍₒ) (h0 : f (γ 0) = 0)
    (hlim : Tendsto (fun t ↦ f (γ t)) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun t ↦ F (γ t)) (𝓝[>] 0)
      (𝓝 (F (γ b) - ∫ t in (0 : ℝ)..b, γ' t * f (γ t))) := by
  set g : ℝ → ℂ := fun t ↦ γ' t * f (γ t)
  have hg : ContinuousOn g (Icc 0 b) := by
    intro t ht
    rcases ht.1.eq_or_lt with rfl | hpos
    · have h0' : ContinuousWithinAt (fun t ↦ f (γ t)) (Ici 0) 0 := by
        rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt, h0]
        exact hlim
      exact hγ'.continuousWithinAt.mul (h0'.mono Icc_subset_Ici_self)
    · exact (hγ'.continuousAt.mul ((hf.continuousAt (isOpen_upperHalfPlaneSet.mem_nhds
        (hγ t ⟨hpos, ht.2⟩))).comp (hd t).continuousAt)).continuousWithinAt
  have hcont := intervalIntegral.continuousOn_primitive_interval_left
    (μ := MeasureTheory.volume) (a := 0) (b := b)
    (by rw [uIcc_of_le hb.le]; exact hg.integrableOn_Icc)
  have h1 : Tendsto (fun ε ↦ ∫ t in ε..b, g t) (𝓝[>] 0) (𝓝 (∫ t in (0 : ℝ)..b, g t)) := by
    rw [← nhdsWithin_Ioo_eq_nhdsGT hb]
    exact (hcont 0 left_mem_uIcc).tendsto.mono_left
      (nhdsWithin_mono _ (by rw [uIcc_of_le hb.le]; exact Ioo_subset_Icc_self))
  have h2 : ∀ᶠ ε in 𝓝[>] 0, ∫ t in ε..b, g t = F (γ b) - F (γ ε) := by
    filter_upwards [Ioo_mem_nhdsGT hb] with ε hε
    exact integral_curve_eq_sub hf hF hε.2.le hd hγ'
      fun t ht ↦ hγ t ⟨hε.1.trans_le ht.1, ht.2⟩
  exact (tendsto_const_nhds.sub h1).congr' (h2.mono fun ε h ↦ by rw [h]; ring)

/-! ### The arc integrals `I₁'_arc` and `I₂'_arc` -/

lemma w₁_mem {θ : ℝ} (h₀ : 0 < θ) (h₁ : θ ≤ π / 2) : w₁ θ ∈ ℍₒ := by
  have : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h₀ (by linarith [pi_pos])
  simp [w₁, circleMap, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  positivity

lemma w₂_mem {θ : ℝ} (h₀ : 0 ≤ θ) (h₁ : θ ≤ π / 2) : w₂ θ ∈ ℍₒ := by
  have : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h₀ (by linarith [pi_pos])
  simp [w₂, circleMap, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  positivity

/-- The arc `w₂` lies entirely in the upper half plane, so `I₂'_arc` is just the difference of the
values of the primitive at the endpoints `i` and `(1 + i)/2`. -/
theorem I₂'_arc_eq_sub : I₂'_arc r = F r I - F r ((1 + I) / 2) := by
  rw [I₂'_arc, Ψ₂'_eq_Φ₃']
  have h := integral_curve_eq_sub (Φ₃'_holo (r := r)).continuousOn
    (fun _ hz ↦ hasDerivAt_F r hz) (by positivity : (0 : ℝ) ≤ π / 2)
    (hasDerivAt_circleMap (I / 2) (1 / 2)) (by fun_prop) fun θ hθ ↦ w₂_mem hθ.1 hθ.2
  rw [show circleMap (I / 2) (1 / 2) (π / 2) = I from w₂_pi_div_two,
    show circleMap (I / 2) (1 / 2) 0 = (1 + I) / 2 from w₂_zero] at h
  exact h

lemma Ψ₁'_w₁_zero : Ψ₁' r (w₁ 0) = 0 := by
  simp [Ψ₁', w₁_zero]

/-- If the integrand `Ψ₁'` tends to `0` as `w → 1` along the arc `w₁` (i.e. it extends continuously
by `0` at `1`), then `F (w₁ θ) → F ((1 + i)/2) - I₁'_arc` as `θ → 0⁺`. -/
theorem tendsto_F_w₁ (hlim : Tendsto (fun θ ↦ Ψ₁' r (w₁ θ)) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun θ ↦ F r (w₁ θ)) (𝓝[>] 0) (𝓝 (F r ((1 + I) / 2) - I₁'_arc r)) := by
  rw [I₁'_arc]
  rw [Ψ₁'_eq_Φ₃'] at hlim ⊢
  have h := tendsto_primitive_curve (Φ₃'_holo (r := r)).continuousOn
    (fun _ hz ↦ hasDerivAt_F r hz) (by positivity : (0 : ℝ) < π / 2)
    (hasDerivAt_circleMap (1 / 2) (1 / 2)) (by fun_prop) (fun θ hθ ↦ w₁_mem hθ.1 hθ.2)
    (Ψ₁'_eq_Φ₃' r ▸ Ψ₁'_w₁_zero r) hlim
  rwa [show circleMap (1 / 2) (1 / 2) (π / 2) = (1 + I) / 2 from w₁_pi_div_two] at h

/-- `I₁'_arc` as the difference between the primitive at `(1 + i)/2` and its limit as one
approaches `1` along the arc `w₁`, assuming the integrand vanishes in the limit. -/
theorem I₁'_arc_eq_sub_lim (hlim : Tendsto (fun θ ↦ Ψ₁' r (w₁ θ)) (𝓝[>] 0) (𝓝 0)) :
    I₁'_arc r = F r ((1 + I) / 2) - limUnder (𝓝[>] 0) (fun θ ↦ F r (w₁ θ)) := by
  rw [(tendsto_F_w₁ r hlim).limUnder_eq]
  ring

/-! ### The segment integrals `I₃'` and `I₄'`

These are the original definitions from `SpherePacking.MagicFunction.a.Defs`:
`I₃' r = ∫_1^{1+i} Φ₃' r z dz` along the vertical segment `z₃' t = 1 + i t`, and
`I₄' r = ∫_{1+i}^{i} Φ₄' r z dz` along the horizontal segment `z₄' t = 1 - t + i`. -/

/-- The vertical segment `t ↦ 1 + i t` (agreeing with `z₃'` on `[0, 1]`). -/
private def ℓ₃ (t : ℝ) : ℂ := 1 + I * t

/-- The horizontal segment `t ↦ 1 - t + i` (agreeing with `z₄'` on `[0, 1]`). -/
private def ℓ₄ (t : ℝ) : ℂ := 1 - t + I

private lemma hasDerivAt_ℓ₃ (t : ℝ) : HasDerivAt ℓ₃ I t := by
  exact (((hasDerivAt_id t).ofReal_comp.const_mul I).const_add 1).congr_deriv (by simp)

private lemma hasDerivAt_ℓ₄ (t : ℝ) : HasDerivAt ℓ₄ (-1) t := by
  exact (((hasDerivAt_id t).ofReal_comp.const_sub 1).add_const I).congr_deriv (by simp)

private lemma I₃'_eq_ℓ₃ : I₃' r = ∫ t in (0 : ℝ)..1, (fun _ ↦ I) t * Φ₃' r (ℓ₃ t) :=
  intervalIntegral.integral_congr fun t ht ↦ by
    rw [uIcc_of_le zero_le_one] at ht
    simp only [Φ₃, ℓ₃, z₃'_eq_of_mem ht]

private lemma I₄'_eq_ℓ₄ : I₄' r = ∫ t in (0 : ℝ)..1, (fun _ ↦ -1) t * Φ₄' r (ℓ₄ t) :=
  intervalIntegral.integral_congr fun t ht ↦ by
    rw [uIcc_of_le zero_le_one] at ht
    simp only [Φ₄, ℓ₄, z₄'_eq_of_mem ht]

/-- The segment `z₄'` lies entirely in the upper half plane, so `I₄'` is just the difference of the
values of the primitive at the endpoints `i` and `1 + i`. -/
theorem I₄'_eq_sub : I₄' r = F r I - F r (1 + I) := by
  rw [I₄'_eq_ℓ₄, Φ₄'_eq_Φ₃', integral_curve_eq_sub (Φ₃'_holo (r := r)).continuousOn
    (fun _ hz ↦ hasDerivAt_F r hz) zero_le_one hasDerivAt_ℓ₄ continuous_const
    fun t ht ↦ by simp [ℓ₄]]
  simp [ℓ₄]

lemma Φ₃'_z₃'_zero : Φ₃' r (z₃' 0) = 0 := by
  simp [Φ₃', z₃'_eq_of_mem (left_mem_Icc.2 zero_le_one)]

/-- If the integrand `Φ₃'` tends to `0` as `z → 1` along the segment `z₃'` (i.e. it extends
continuously by `0` at `1`), then `F (z₃' t) → F (1 + i) - I₃'` as `t → 0⁺`. -/
theorem tendsto_F_z₃' (hlim : Tendsto (fun t ↦ Φ₃' r (z₃' t)) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun t ↦ F r (z₃' t)) (𝓝[>] 0) (𝓝 (F r (1 + I) - I₃' r)) := by
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), z₃' t = ℓ₃ t := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
    exact z₃'_eq_of_mem (Ioo_subset_Icc_self ht)
  have h := tendsto_primitive_curve (Φ₃'_holo (r := r)).continuousOn
    (fun _ hz ↦ hasDerivAt_F r hz) zero_lt_one hasDerivAt_ℓ₃ continuous_const
    (fun t ht ↦ by simpa [ℓ₃] using ht.1)
    (by simp [Φ₃', ℓ₃])
    (hlim.congr' (hev.mono fun t ht ↦ by rw [ht]))
  rw [← I₃'_eq_ℓ₃, show ℓ₃ 1 = 1 + I by simp [ℓ₃]] at h
  exact h.congr' (hev.mono fun t ht ↦ by simp only [ht])

/-- `I₃'` as the difference between the primitive at `1 + i` and its limit as one approaches `1`
along the segment `z₃'`, assuming the integrand vanishes in the limit. -/
theorem I₃'_eq_sub_lim (hlim : Tendsto (fun t ↦ Φ₃' r (z₃' t)) (𝓝[>] 0) (𝓝 0)) :
    I₃' r = F r (1 + I) - limUnder (𝓝[>] 0) (fun t ↦ F r (z₃' t)) := by
  rw [(tendsto_F_z₃' r hlim).limUnder_eq]
  ring

/-! ### Comparison: `I₁'_arc + I₂'_arc = I₃' + I₄'` -/

/-- The integrand `Φ₃'` is bounded on a closed disc tangent to the real line at `1`, namely
`closedBall (1 + i/2) (1/2)`. Under `τ = -1/(z - 1)` this disc (minus `1`) is mapped into the half
plane `Im τ ≥ 1`, where `|φ₀ τ| ≤ C₀ e^{-2π Im τ} ≤ C₀` (`norm_φ₀_le`, the blueprint's
`cor:phi0-bound`); moreover `|z - 1| ≤ 1` and `|e^{πirz}| ≤ e^{π|r|}` on the disc. -/
lemma norm_Φ₃'_le_near_one :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ Metric.closedBall (1 + (ρ : ℂ) * I) ρ, ‖Φ₃' r z‖ ≤ C * ‖z - 1‖ ^ 2 := by
  obtain ⟨C₀, hC₀, hφ₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  have hM : 0 ≤ C₀ * Real.exp (π * |r|) := by positivity
  refine ⟨1 / 2, by norm_num, le_rfl, C₀ * Real.exp (π * |r|), hM, fun z hz ↦ ?_⟩
  -- The disc condition: `|z - 1|² ≤ Im z`.
  have hdisc : (z.re - 1) ^ 2 + z.im ^ 2 ≤ z.im := by
    rw [Metric.mem_closedBall, dist_eq_norm, ← sq_le_sq₀ (norm_nonneg _) (by norm_num),
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hz
    simp only [sub_re, sub_im, add_re, add_im, one_re, one_im, mul_re, mul_im, ofReal_re,
      ofReal_im, I_re, I_im] at hz
    nlinarith
  have him0 : 0 ≤ z.im := by nlinarith
  have him1 : z.im ≤ 1 := by nlinarith
  by_cases hz1 : z = 1
  · subst hz1; simp [Φ₃']
  have hns : 0 < Complex.normSq (z - 1) := Complex.normSq_pos.2 (sub_ne_zero.2 hz1)
  have hns' : Complex.normSq (z - 1) = (z.re - 1) ^ 2 + z.im ^ 2 := by
    simp [Complex.normSq_apply]; ring
  -- `τ = -1/(z - 1)` has `Im τ = Im z / |z - 1|² ≥ 1`.
  have hτ : 1 ≤ (-1 / (z - 1)).im := by
    have : (-1 / (z - 1)).im = z.im / Complex.normSq (z - 1) := by
      simp [neg_div]
    rw [this, le_div_iff₀ hns, one_mul, hns']
    exact hdisc
  have hτpos : 0 < (-1 / (z - 1)).im := by linarith
  have hφ : ‖φ₀'' (-1 / (z - 1))‖ ≤ C₀ := by
    rw [φ₀''_def hτpos]
    refine (hφ₀ ⟨_, hτpos⟩ (by change 1 / 2 < (-1 / (z - 1)).im; linarith)).trans ?_
    refine mul_le_of_le_one_right hC₀.le (Real.exp_le_one_iff.2 ?_)
    change -2 * π * (-1 / (z - 1)).im ≤ 0
    nlinarith [pi_pos]
  have hexp : ‖cexp (π * I * r * z)‖ ≤ Real.exp (π * |r|) := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.2 ?_
    simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im]
    have h1 : -r ≤ |r| := neg_le_abs r
    have h2 : 0 ≤ |r| := abs_nonneg r
    nlinarith [pi_pos, mul_le_mul_of_nonneg_left h1 him0, mul_le_mul_of_nonneg_left him1 h2]
  calc ‖Φ₃' r z‖ = ‖φ₀'' (-1 / (z - 1))‖ * ‖(z - 1) ^ 2‖ * ‖cexp (π * I * r * z)‖ := by
        simp only [Φ₃', norm_mul]
    _ ≤ C₀ * ‖z - 1‖ ^ 2 * Real.exp (π * |r|) := by rw [norm_pow]; gcongr
    _ = C₀ * Real.exp (π * |r|) * ‖z - 1‖ ^ 2 := by ring

/-- In particular, `Φ₃'` is bounded on a closed disc tangent to the real line at `1`. -/
lemma Φ₃'_bounded_near_one :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ M : ℝ, ∀ z ∈ Metric.closedBall (1 + (ρ : ℂ) * I) ρ, ‖Φ₃' r z‖ ≤ M := by
  obtain ⟨ρ, hρ, hρ', C, hC, h⟩ := norm_Φ₃'_le_near_one r
  refine ⟨ρ, hρ, C, fun z hz ↦ (h z hz).trans ?_⟩
  have h1 : ‖z - 1‖ ≤ 1 := by
    have h2 : ‖z - 1‖ ≤ ‖z - (1 + (ρ : ℂ) * I)‖ + ‖(ρ : ℂ) * I‖ := by
      have := norm_add_le (z - (1 + (ρ : ℂ) * I)) ((ρ : ℂ) * I)
      rwa [show z - (1 + (ρ : ℂ) * I) + (ρ : ℂ) * I = z - 1 by ring] at this
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    simp only [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos hρ] at h2
    linarith
  calc C * ‖z - 1‖ ^ 2 ≤ C * 1 := by gcongr; exact pow_le_one₀ (norm_nonneg _) h1
    _ = C := mul_one C

/-- The difference of the values of the primitive at two points of the upper half plane is the
integral along the segment joining them. -/
lemma F_sub_eq_integral_segment {a b : ℂ} (ha : a ∈ ℍₒ) (hb : b ∈ ℍₒ) :
    F r a - F r b = ∫ t in (0 : ℝ)..1, (a - b) * Φ₃' r (b + t * (a - b)) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ ↦ b + t * (a - b)) (a - b) t := fun t ↦
    (((hasDerivAt_id t).ofReal_comp.mul_const (a - b)).const_add b).congr_deriv (by simp)
  have h := integral_curve_eq_sub (Φ₃'_holo (r := r)).continuousOn
    (fun _ hz ↦ hasDerivAt_F r hz) zero_le_one hd continuous_const fun t ht ↦ by
      simpa [Complex.real_smul] using (convex_halfSpace_im_gt 0).add_smul_sub_mem hb ha ht
  simp only [ofReal_one, one_mul, ofReal_zero, zero_mul, add_zero, add_sub_cancel] at h
  exact h.symm

/-- If `|Φ₃'| ≤ M` on a closed disc `D`, then for `a, b ∈ D ∩ ℍ` the integral along the segment
`[b, a]`, hence the difference of the values of the primitive, is bounded by `M |a - b|`. -/
lemma norm_F_sub_le {c : ℂ} {ρ M : ℝ} (hM : ∀ z ∈ Metric.closedBall c ρ, ‖Φ₃' r z‖ ≤ M)
    {a b : ℂ} (ha : a ∈ ℍₒ) (hb : b ∈ ℍₒ) (ha' : a ∈ Metric.closedBall c ρ)
    (hb' : b ∈ Metric.closedBall c ρ) :
    ‖F r a - F r b‖ ≤ M * ‖a - b‖ := by
  rw [F_sub_eq_integral_segment r ha hb]
  calc ‖∫ t in (0 : ℝ)..1, (a - b) * Φ₃' r (b + t * (a - b))‖ ≤ ‖a - b‖ * M * |1 - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const fun t ht ↦ ?_
    _ = M * ‖a - b‖ := by simp [mul_comm]
  rw [uIoc_of_le zero_le_one] at ht
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left (hM _ ?_) (norm_nonneg _)
  simpa [Complex.real_smul] using
    (convex_closedBall c ρ).add_smul_sub_mem hb' ha' (Ioc_subset_Icc_self ht)

/-- The arc `w₁` eventually lies in any disc tangent to the real line at `1`. -/
lemma w₁_mem_closedBall {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (hερ : ε ≤ ρ) (hεπ : ε ≤ π / 2) :
    w₁ ε ∈ Metric.closedBall (1 + ρ * I) ρ := by
  have hre : (w₁ ε).re = 1 / 2 + Real.cos ε / 2 := by
    simp [w₁, circleMap, exp_mul_I, ← ofReal_cos, ← ofReal_sin]; ring
  have him : (w₁ ε).im = Real.sin ε / 2 := by
    simp [w₁, circleMap, exp_mul_I, ← ofReal_cos, ← ofReal_sin]; ring
  rw [Metric.mem_closedBall, dist_eq_norm, ← sq_le_sq₀ (norm_nonneg _) hρ.le,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [sub_re, sub_im, add_re, add_im, one_re, one_im, mul_re, mul_im, ofReal_re, ofReal_im,
    I_re, I_im, hre, him]
  have hc := Real.sin_sq_add_cos_sq ε
  have h1 : 1 - ε ^ 2 / 2 ≤ Real.cos ε := Real.one_sub_sq_div_two_le_cos
  have h2 : 2 / π * ε ≤ Real.sin ε := Real.mul_le_sin hε.le hεπ
  have h3 : 1 / 2 ≤ 2 / π := by
    rw [le_div_iff₀ pi_pos]; linarith [pi_le_four]
  have hs : ε ^ 2 / 2 ≤ ρ * Real.sin ε :=
    calc ε ^ 2 / 2 = ε * (1 / 2 * ε) := by ring
      _ ≤ ρ * (2 / π * ε) := mul_le_mul hερ (by gcongr) (by positivity) hρ.le
      _ ≤ ρ * Real.sin ε := mul_le_mul_of_nonneg_left h2 hρ.le
  nlinarith

/-- The segment `z₃'` eventually lies in any disc tangent to the real line at `1`. -/
lemma z₃'_mem_closedBall {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (hερ : ε ≤ ρ) (hε1 : ε ≤ 1) :
    z₃' ε ∈ Metric.closedBall (1 + ρ * I) ρ := by
  rw [z₃'_eq_of_mem ⟨hε.le, hε1⟩, Metric.mem_closedBall, dist_eq_norm,
    show 1 + I * ε - (1 + ρ * I) = ((ε - ρ : ℝ) : ℂ) * I by push_cast; ring, norm_mul,
    norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

lemma tendsto_w₁_one : Tendsto w₁ (𝓝[>] 0) (𝓝 1) := by
  rw [← w₁_zero]
  exact (continuous_circleMap _ _).continuousAt.tendsto.mono_left nhdsWithin_le_nhds

lemma tendsto_z₃'_one : Tendsto z₃' (𝓝[>] 0) (𝓝 1) := by
  have h : Tendsto ℓ₃ (𝓝[>] 0) (𝓝 1) := by
    have : Continuous ℓ₃ := by unfold ℓ₃; fun_prop
    simpa [ℓ₃] using this.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)))
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
  exact (z₃'_eq_of_mem (Ioo_subset_Icc_self ht)).symm

/-- Taking the two limits independently, in variables `ε₁` (along `w₁`) and `ε₂` (along `z₃'`),
the difference of the values of the primitive tends to `0`. -/
theorem tendsto_F_w₁_sub_F_z₃' :
    Tendsto (fun ε : ℝ × ℝ ↦ F r (w₁ ε.1) - F r (z₃' ε.2)) (𝓝[>] 0 ×ˢ 𝓝[>] 0) (𝓝 0) := by
  obtain ⟨ρ, hρ, M, hM⟩ := Φ₃'_bounded_near_one r
  have hbound : ∀ᶠ ε : ℝ × ℝ in 𝓝[>] 0 ×ˢ 𝓝[>] 0,
      ‖F r (w₁ ε.1) - F r (z₃' ε.2)‖ ≤ M * ‖w₁ ε.1 - z₃' ε.2‖ := by
    have h₁ : Ioo 0 (min ρ (π / 2)) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by positivity)
    have h₂ : Ioo 0 (min ρ 1) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by positivity)
    filter_upwards [prod_mem_prod h₁ h₂] with ε hε
    obtain ⟨⟨h₁0, h₁1⟩, ⟨h₂0, h₂1⟩⟩ := hε
    exact norm_F_sub_le r hM (w₁_mem h₁0 ((h₁1.trans_le (min_le_right _ _)).le))
      (z₃'_mem_upperHalfPlane_set ⟨h₂0, (h₂1.trans_le (min_le_right _ _)).le⟩)
      (w₁_mem_closedBall hρ h₁0 (h₁1.trans_le (min_le_left _ _)).le
        (h₁1.trans_le (min_le_right _ _)).le)
      (z₃'_mem_closedBall hρ h₂0 (h₂1.trans_le (min_le_left _ _)).le
        (h₂1.trans_le (min_le_right _ _)).le)
  have hlim : Tendsto (fun ε : ℝ × ℝ ↦ M * ‖w₁ ε.1 - z₃' ε.2‖) (𝓝[>] 0 ×ˢ 𝓝[>] 0) (𝓝 0) := by
    have := ((tendsto_w₁_one.comp tendsto_fst).sub (tendsto_z₃'_one.comp tendsto_snd)).norm
    simpa using this.const_mul M
  exact squeeze_zero_norm' hbound hlim

/-- The limits of the common primitive `F` at `1` along the arc `w₁` and along the segment `z₃'`
agree. -/
theorem lim_F_w₁_eq_lim_F_z₃' (hlim₁ : Tendsto (fun θ ↦ Ψ₁' r (w₁ θ)) (𝓝[>] 0) (𝓝 0))
    (hlim₃ : Tendsto (fun t ↦ Φ₃' r (z₃' t)) (𝓝[>] 0) (𝓝 0)) :
    limUnder (𝓝[>] 0) (fun θ ↦ F r (w₁ θ)) = limUnder (𝓝[>] 0) (fun t ↦ F r (z₃' t)) := by
  have h₁ := tendsto_F_w₁ r hlim₁
  have h₃ := tendsto_F_z₃' r hlim₃
  rw [h₁.limUnder_eq, h₃.limUnder_eq]
  exact sub_eq_zero.1 <| tendsto_nhds_unique ((h₁.comp tendsto_fst).sub (h₃.comp tendsto_snd))
    (tendsto_F_w₁_sub_F_z₃' r)

/-- The integrand vanishes as one approaches `1` along any curve that eventually enters every disc
tangent to the real line at `1`, since `‖Φ₃' r z‖ ≤ C ‖z - 1‖²` on such a disc. -/
lemma tendsto_Φ₃'_curve {γ : ℝ → ℂ} (hγ : Tendsto γ (𝓝[>] 0) (𝓝 1))
    (hmem : ∀ ρ : ℝ, 0 < ρ → ∀ᶠ t in 𝓝[>] 0, γ t ∈ Metric.closedBall (1 + (ρ : ℂ) * I) ρ) :
    Tendsto (fun t ↦ Φ₃' r (γ t)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨ρ, hρ, -, C, -, h⟩ := norm_Φ₃'_le_near_one r
  refine squeeze_zero_norm' ((hmem ρ hρ).mono fun t ht ↦ h _ ht) ?_
  simpa using (((hγ.sub_const 1).norm).pow 2).const_mul C

/-- The integrand `Ψ₁'` vanishes as one approaches `1` along the arc `w₁`. -/
theorem tendsto_Ψ₁'_w₁ : Tendsto (fun θ ↦ Ψ₁' r (w₁ θ)) (𝓝[>] 0) (𝓝 0) := by
  rw [Ψ₁'_eq_Φ₃']
  refine tendsto_Φ₃'_curve r tendsto_w₁_one fun ρ hρ ↦ ?_
  filter_upwards [Ioo_mem_nhdsGT (show 0 < min ρ (π / 2) by positivity)] with t ht
  exact w₁_mem_closedBall hρ ht.1 (ht.2.le.trans (min_le_left _ _))
    (ht.2.le.trans (min_le_right _ _))

/-- The integrand `Φ₃'` vanishes as one approaches `1` along the segment `z₃'`. -/
theorem tendsto_Φ₃'_z₃' : Tendsto (fun t ↦ Φ₃' r (z₃' t)) (𝓝[>] 0) (𝓝 0) := by
  refine tendsto_Φ₃'_curve r tendsto_z₃'_one fun ρ hρ ↦ ?_
  filter_upwards [Ioo_mem_nhdsGT (show 0 < min ρ 1 by positivity)] with t ht
  exact z₃'_mem_closedBall hρ ht.1 (ht.2.le.trans (min_le_left _ _))
    (ht.2.le.trans (min_le_right _ _))

/-- The (radial profile of the) Fourier transform of `I₁ + I₂` is `I₃' + I₄'`. -/
theorem I₁'_arc_add_I₂'_arc_eq : I₁'_arc r + I₂'_arc r = I₃' r + I₄' r := by
  rw [I₁'_arc_eq_sub_lim r (tendsto_Ψ₁'_w₁ r), I₂'_arc_eq_sub, I₃'_eq_sub_lim r (tendsto_Φ₃'_z₃' r),
    I₄'_eq_sub, lim_F_w₁_eq_lim_F_z₃' r (tendsto_Ψ₁'_w₁ r) (tendsto_Φ₃'_z₃' r)]
  ring

open scoped FourierTransform in
/-- The Fourier transform of `I₁ + I₂` is `I₃ + I₄`, pointwise. -/
theorem fourier_I₁_add_fourier_I₂ (ξ : EuclideanSpace ℝ (Fin 8)) :
    𝓕 MagicFunction.a.RadialFunctions.I₁ ξ + 𝓕 MagicFunction.a.RadialFunctions.I₂ ξ =
      MagicFunction.a.RadialFunctions.I₃ ξ + MagicFunction.a.RadialFunctions.I₄ ξ := by
  rw [fourier_I₁_eq, fourier_I₂_eq, I₁'_arc_add_I₂'_arc_eq]
  rfl

end Primitive

end MagicFunction.a.ArcIntegrals

end
