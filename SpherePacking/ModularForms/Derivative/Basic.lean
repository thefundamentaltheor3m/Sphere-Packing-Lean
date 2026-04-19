module
public import SpherePacking.ModularForms.EisensteinBase
public import SpherePacking.ModularForms.CuspFormIsoModforms
public import SpherePacking.ModularForms.Delta
public import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.Complex.Liouville
import SpherePacking.ModularForms.Lv1Lv2Identities
import SpherePacking.Tactic.NormNumI
public import Mathlib.NumberTheory.ModularForms.SlashActions
public import SpherePacking.ForMathlib.Cusps

@[expose] public section

/-!
# The derivative operator `D` on modular forms (fundamentals)

This file defines the derivative operator `D F z = (2πi)⁻¹ · deriv(F ∘ ofComplex) z` on functions
`ℍ → ℂ`, and establishes its basic algebraic properties (linearity, Leibniz rule), the termwise
differentiation of q-series (Lemma 6.45), and Cauchy-style estimates giving bounded-at-infinity
consequences for the D-derivative of a bounded holomorphic function.
-/

open scoped ModularForm MatrixGroups Manifold Topology BigOperators

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap ModularForm
open ModularFormClass
open Metric Filter Function

/-!
Definition of (Serre) derivative of modular forms.
Prove Ramanujan's formulas on derivatives of Eisenstein series.
-/
@[expose] public noncomputable def D (F : ℍ → ℂ) : ℍ → ℂ :=
  fun (z : ℍ) => (2 * π * I)⁻¹ * ((deriv (F ∘ ofComplex)) z)

/-- Bridge lemma: MDifferentiability on `ℍ` gives differentiability of `F ∘ ofComplex`. -/
public lemma MDifferentiableAt_DifferentiableAt {F : ℍ → ℂ} {z : ℍ}
  (h : MDiffAt F z) :
  DifferentiableAt ℂ (F ∘ ofComplex) ↑z :=
  mdifferentiableAt_iff.mp h

/--
The converse direction: `DifferentiableAt` on ℂ implies `MDifferentiableAt` on ℍ.
-/
public lemma DifferentiableAt_MDifferentiableAt {G : ℂ → ℂ} {z : ℍ}
  (h : DifferentiableAt ℂ G ↑z) :
  MDiffAt (G ∘ (↑) : ℍ → ℂ) z := by
  rw [mdifferentiableAt_iff]
  refine h.congr_of_eventuallyEq <| Filter.eventuallyEq_of_mem (isOpen_upperHalfPlaneSet.mem_nhds
    z.im_pos) (by intro w hw; simp [Function.comp, ofComplex_apply_of_im_pos hw])

/--
The derivative operator `D` preserves MDifferentiability.
If `F : ℍ → ℂ` is MDifferentiable, then `D F` is also MDifferentiable.
-/
public theorem D_differentiable {F : ℍ → ℂ} (hF : MDiff F) : MDiff (D F) := fun z =>
  MDifferentiableAt.mul mdifferentiableAt_const <| DifferentiableAt_MDifferentiableAt <|
    ((UpperHalfPlane.mdifferentiable_iff.mp hF).deriv isOpen_upperHalfPlaneSet).differentiableAt
      (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)

/-- MDifferentiability of `E₂`.
TODO: Move this to E2.lean. -/
public theorem E₂_holo' : MDiff E₂ := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hη : DifferentiableOn ℂ η {z : ℂ | 0 < z.im} := by
    intro z hz
    have hz' : DifferentiableAt ℂ η z := by
      simpa [η] using (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet (z := z) hz)
    exact hz'.differentiableWithinAt
  have hlog : DifferentiableOn ℂ (logDeriv η) {z | 0 < z.im} :=
    (hη.deriv isOpen_upperHalfPlaneSet).div hη fun z hz => by
      simpa [η] using (ModularForm.eta_ne_zero (z := z) hz)
  exact (hlog.const_mul ((↑π * I / 12)⁻¹)).congr fun z hz => by
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz,
      show logDeriv η z = (↑π * I / 12) * E₂ ⟨z, hz⟩ by
        simpa [η, E₂] using (ModularForm.logDeriv_eta_eq_E2 ⟨z, hz⟩)]
    field_simp [Real.pi_ne_zero]

/--
Basic properties of derivatives: linearity, Leibniz rule, etc.
-/
@[simp]
public theorem D_add (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    D (F + G) = D F + D G := by
  ext z
  simpa [D, mul_add] using congrArg ((2 * π * I)⁻¹ * ·)
    (deriv_add (MDifferentiableAt_DifferentiableAt (hF z))
      (MDifferentiableAt_DifferentiableAt (hG z)))


/-- Compatibility of `D` with negation. -/
@[simp]
public theorem D_neg (F : ℍ → ℂ) (hF : MDiff F) : D (-F) = -D F := by
  ext z
  have hderiv : deriv ((-F) ∘ ofComplex) (z : ℂ) = -deriv (F ∘ ofComplex) (z : ℂ) :=
    (MDifferentiableAt_DifferentiableAt (hF z)).hasDerivAt.neg.deriv
  simp [D, hderiv, mul_assoc]


/-- Compatibility of `D` with subtraction. -/
@[simp]
public theorem D_sub (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G)
    : D (F - G) = D F - D G := by
  simpa [sub_eq_add_neg, D_neg (F := G) hG] using D_add F (-G) hF hG.neg


/-- Compatibility of `D` with scalar multiplication. -/
@[simp]
public theorem D_smul (c : ℂ) (F : ℍ → ℂ) : D (c • F) = c • D F := by
  ext z
  have hderiv : deriv ((c • F) ∘ ofComplex) (z : ℂ) = c • deriv (F ∘ ofComplex) z := by
    simpa [Pi.smul_apply] using (deriv_const_smul_field (x := (z : ℂ)) c (F ∘ ofComplex))
  simp [D, hderiv, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]


/-- Leibniz rule for `D`. -/
@[simp]
public theorem D_mul (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G)
    : D (F * G) = D F * G + F * D G := by
  ext z
  have hderiv : deriv ((F * G) ∘ ofComplex) z =
      deriv (F ∘ ofComplex) z * G z + F z * deriv (G ∘ ofComplex) z := by
    simpa [Function.comp_apply, ofComplex_apply] using
      deriv_mul (MDifferentiableAt_DifferentiableAt (hF z))
        (MDifferentiableAt_DifferentiableAt (hG z))
  simp [D, hderiv, mul_add, mul_assoc, mul_left_comm, mul_comm]

/-! ### Termwise differentiation of q-series (Lemma 6.45) -/

/-- Helper: HasDerivAt for a·exp(2πicw) with chain rule. -/
lemma hasDerivAt_qexp (a c w : ℂ) :
    HasDerivAt (fun z => a * cexp (2 * π * I * c * z))
      (a * (2 * π * I * c) * cexp (2 * π * I * c * w)) w := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    ((Complex.hasDerivAt_exp (2 * π * I * c * w)).scomp w
      ((hasDerivAt_id w).const_mul (2 * π * I * c))).const_mul a

/-- Helper: derivWithin for qexp term on upper half-plane. -/
lemma derivWithin_qexp (a c : ℂ) (w : ℂ) (hw : 0 < w.im) :
    derivWithin (fun z => a * cexp (2 * π * I * c * z))
      {z : ℂ | 0 < z.im} w = a * (2 * π * I * c) * cexp (2 * π * I * c * w) :=
  ((hasDerivAt_qexp a c w).hasDerivWithinAt).derivWithin
    (isOpen_upperHalfPlaneSet.uniqueDiffWithinAt hw)

/--
**Lemma 6.45 (Blueprint)**: $D$ commutes with tsum for $q$-series.
If F(z) = Σ a(n)·qⁿ where q = exp(2πiz), then D F(z) = Σ n·a(n)·qⁿ.

More precisely, this lemma shows that for a ℕ-indexed q-series with summable coefficients
satisfying appropriate derivative bounds, D acts termwise by multiplying coefficients by n.
-/
public theorem D_qexp_tsum (a : ℕ → ℂ) (z : ℍ)
    (hsum_deriv : ∀ K : Set ℂ, K ⊆ {w : ℂ | 0 < w.im} → IsCompact K →
        ∃ u : ℕ → ℝ, Summable u ∧ ∀ n (k : K), ‖a n * (2 * π * I * n) *
          cexp (2 * π * I * n * k.1)‖ ≤ u n) :
    D (fun w => ∑' n, a n * cexp (2 * π * I * n * w)) z =
      ∑' n : ℕ, (n : ℂ) * a n * cexp (2 * π * I * n * z) := by
  simp only [D]
  -- Each term is differentiable
  have hf_diff : ∀ n (r : {w : ℂ | 0 < w.im}), DifferentiableAt ℂ
      (fun w => a n * cexp (2 * π * I * n * w)) r := fun n r =>
    ((differentiableAt_id.const_mul (2 * π * I * n)).cexp).const_mul (a n)
  -- Summability at each point (bound holds for n ≥ 1, exception set ⊆ {0})
  have hf_sum : ∀ y : ℂ, y ∈ {w : ℂ | 0 < w.im} →
      Summable (fun n => a n * cexp (2 * π * I * n * y)) := by
    intro y hy
    obtain ⟨u, hu_sum, hu_bound⟩ :=
      hsum_deriv {y} (Set.singleton_subset_iff.mpr hy) isCompact_singleton
    apply Summable.of_norm_bounded_eventually (g := fun n => u n / (2 * π)) (hu_sum.div_const _)
    rw [Filter.eventually_cofinite]
    refine Set.Finite.subset (Set.finite_singleton 0) fun n hn => ?_
    simp only [Set.mem_setOf_eq, not_le] at hn
    by_contra h_ne
    have h_deriv_bound := hu_bound n ⟨y, Set.mem_singleton y⟩
    have h_n_ge_1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr h_ne)
    have h_norm_2pin : ‖(2 : ℂ) * π * I * n‖ = 2 * π * n := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
          Complex.norm_I, mul_one, Complex.norm_natCast, Real.norm_of_nonneg pi_pos.le]
    have h_bound : ‖a n * cexp (2 * π * I * n * y)‖ ≤ u n / (2 * π) := by
      have h_pos : (0 : ℝ) < 2 * π * n := by positivity
      have h_key : ‖a n * cexp (2 * π * I * n * y)‖ * (2 * π * n) =
          ‖a n * (2 * π * I * n) * cexp (2 * π * I * n * y)‖ := by
        simp only [norm_mul, h_norm_2pin]; ring
      calc ‖a n * cexp (2 * π * I * n * y)‖
          = ‖a n * cexp (2 * π * I * n * y)‖ * (2 * π * n) / (2 * π * n) := by field_simp
        _ = ‖a n * (2 * π * I * n) * cexp (2 * π * I * n * y)‖ / (2 * π * n) := by
            rw [h_key]
        _ ≤ u n / (2 * π * n) := div_le_div_of_nonneg_right h_deriv_bound h_pos.le
        _ ≤ u n / (2 * π) := by
            apply div_le_div_of_nonneg_left (le_trans (norm_nonneg _) h_deriv_bound)
              (by positivity); nlinarith
    exact hn.not_ge h_bound
  -- Derivative bound for uniform convergence
  have hu : ∀ K ⊆ {w : ℂ | 0 < w.im}, IsCompact K →
      ∃ u : ℕ → ℝ, Summable u ∧ ∀ n (k : K),
        ‖derivWithin (fun w => a n * cexp (2 * π * I * n * w))
            {w : ℂ | 0 < w.im} k‖ ≤ u n := by
    intro K hK1 hK2
    obtain ⟨u, hu_sum, hu_bound⟩ := hsum_deriv K hK1 hK2
    exact ⟨u, hu_sum, fun n k => by rw [derivWithin_qexp _ _ _ (hK1 k.2)]; exact hu_bound n k⟩
  -- Apply termwise differentiation
  have h_tsum_deriv := hasDerivAt_tsum_fun (fun n w => a n * cexp (2 * π * I * n * w))
    isOpen_upperHalfPlaneSet (z : ℂ) z.2 hf_sum hu hf_diff
  -- The composed function agrees with ℂ → ℂ in a neighborhood
  have h_agree :
      ((fun w : ℍ => ∑' n, a n * cexp (2 * π * I * n * w)) ∘ ofComplex)
        =ᶠ[nhds (z : ℂ)] fun w => ∑' n, a n * cexp (2 * π * I * n * w) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.2] with w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw, UpperHalfPlane.coe_mk]
  rw [h_agree.deriv_eq, h_tsum_deriv.deriv]
  -- Simplify derivWithin using helper
  have h_deriv_simp : ∀ n, derivWithin (fun w => a n * cexp (2 * π * I * n * w))
      {w : ℂ | 0 < w.im} z = a n * (2 * π * I * n) * cexp (2 * π * I * n * z) :=
    fun n => derivWithin_qexp _ _ _ z.2
  simp_rw [h_deriv_simp, ← tsum_mul_left]
  congr 1; funext n; field_simp [two_pi_I_ne_zero]

/-! ## Cauchy estimates for `D` -/

/-- If `f : ℍ → ℂ` is `MDifferentiable` and a closed disk in `ℂ` lies in the upper
half-plane, then `f ∘ ofComplex` is `DiffContOnCl` on the corresponding open disk. -/
public lemma diffContOnCl_comp_ofComplex_of_mdifferentiable {f : ℍ → ℂ}
    (hf : MDiff f) {c : ℂ} {R : ℝ}
    (hclosed : Metric.closedBall c R ⊆ {z : ℂ | 0 < z.im}) :
    DiffContOnCl ℂ (f ∘ ofComplex) (Metric.ball c R) :=
  ⟨fun z hz =>
      (MDifferentiableAt_DifferentiableAt
        (hf ⟨z, hclosed (Metric.ball_subset_closedBall hz)⟩)).differentiableWithinAt,
    fun z hz =>
      (MDifferentiableAt_DifferentiableAt
        (hf ⟨z, hclosed (Metric.closure_ball_subset_closedBall hz)⟩)).continuousAt
        |>.continuousWithinAt⟩

/-- Closed ball centered at z with radius z.im/2 is contained in the upper half plane. -/
public lemma closedBall_center_subset_upperHalfPlane (z : ℍ) :
    Metric.closedBall (z : ℂ) (z.im / 2) ⊆ {w : ℂ | 0 < w.im} := by
  intro w hw
  have hdist : dist w z ≤ z.im / 2 := Metric.mem_closedBall.mp hw
  have habs : |w.im - z.im| ≤ z.im / 2 := by
    simpa [Complex.sub_im] using
      (le_trans (by simpa [dist_eq_norm] using (abs_im_le_norm (w - z))) hdist)
  have hw_im : z.im / 2 ≤ w.im := by linarith [(abs_le.mp habs).1]
  exact lt_of_lt_of_le (by linarith [z.im_pos] : 0 < z.im / 2) hw_im

/-- Cauchy estimate for the D-derivative: if `f ∘ ofComplex` is holomorphic on a disk
of radius `r` around `z` and bounded by `M` on the boundary sphere,
then `‖D f z‖ ≤ M / (2πr)`. -/
public lemma norm_D_le_of_sphere_bound {f : ℍ → ℂ} {z : ℍ} {r M : ℝ}
    (hr : 0 < r) (hDiff : DiffContOnCl ℂ (f ∘ ofComplex) (Metric.ball (z : ℂ) r))
    (hbdd : ∀ w ∈ Metric.sphere (z : ℂ) r, ‖(f ∘ ofComplex) w‖ ≤ M) :
    ‖D f z‖ ≤ M / (2 * π * r) := calc ‖D f z‖
  _ = (2 * π)⁻¹ * ‖deriv (f ∘ ofComplex) z‖ := by simp [D, abs_of_pos Real.pi_pos]
  _ ≤ (2 * π)⁻¹ * (M / r) := by
        gcongr; exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hDiff hbdd
  _ = M / (2 * π * r) := by ring

lemma norm_D_le_div_pi_im_of_bounded {f : ℍ → ℂ}
    (hf : MDiff f) {M A : ℝ}
    (hMA : ∀ z : ℍ, A ≤ z.im → ‖f z‖ ≤ M) {z : ℍ} (hz : 2 * max A 0 + 1 ≤ z.im) :
    ‖D f z‖ ≤ M / (π * z.im) := by
  have hR_pos : 0 < z.im / 2 := by linarith [z.im_pos]
  have hclosed := closedBall_center_subset_upperHalfPlane z
  have hDiff : DiffContOnCl ℂ (f ∘ ofComplex) (Metric.ball (z : ℂ) (z.im / 2)) :=
    diffContOnCl_comp_ofComplex_of_mdifferentiable hf hclosed
  have hf_bdd_sphere :
      ∀ w ∈ Metric.sphere (z : ℂ) (z.im / 2), ‖(f ∘ ofComplex) w‖ ≤ M := by
    intro w hw
    have hw_im_pos : 0 < w.im := hclosed (Metric.sphere_subset_closedBall hw)
    have hdist : dist w z = z.im / 2 := Metric.mem_sphere.mp hw
    have habs : |w.im - z.im| ≤ z.im / 2 := by
      simpa [Complex.sub_im, hdist] using
          (by simpa [dist_eq_norm] using (abs_im_le_norm (w - z)) : |(w - z).im| ≤ dist w z)
    have hmax : max A 0 ≤ z.im / 2 := by linarith [hz]
    have hw_im_ge : z.im / 2 ≤ w.im := by linarith [(abs_le.mp habs).1]
    have hw_im_ge_A : A ≤ w.im := le_trans (le_trans (le_max_left A 0) hmax) hw_im_ge
    simpa [ofComplex_apply_of_im_pos hw_im_pos] using hMA ⟨w, hw_im_pos⟩ hw_im_ge_A
  have hDz : ‖D f z‖ ≤ M / (2 * π * (z.im / 2)) :=
    norm_D_le_of_sphere_bound hR_pos hDiff hf_bdd_sphere
  simpa [div_eq_mul_inv] using (hDz.trans_eq (by ring))

/-- The D-derivative is bounded at infinity for bounded holomorphic functions.

For y large (y ≥ 2·max(A,0) + 1), we use a ball of radius z.im/2 around z.
The ball lies in the upper half plane, f is bounded by M on it, and
`norm_D_le_of_sphere_bound` gives ‖D f z‖ ≤ M/(π·z.im) ≤ M/π. -/
public lemma D_isBoundedAtImInfty_of_bounded {f : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbdd : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (D f) := by
  rw [isBoundedAtImInfty_iff] at hbdd ⊢
  obtain ⟨M, A, hMA⟩ := hbdd
  refine ⟨M / π, 2 * max A 0 + 1, ?_⟩
  intro z hz
  have hz_im_ge_1 : 1 ≤ z.im := by linarith [le_max_right A 0, hz]
  have hM_nonneg : 0 ≤ M :=
    (norm_nonneg _).trans (hMA z (by linarith [le_max_left A 0, hz]))
  calc
    ‖D f z‖ ≤ M / (π * z.im) := norm_D_le_div_pi_im_of_bounded hf hMA hz
    _ ≤ M / (π * 1) := by gcongr
    _ = M / π := by ring

/-- The D-derivative of a bounded holomorphic function tends to zero at infinity.

For z with im(z) = y, a Cauchy estimate on a ball of radius y/2 gives
‖D f z‖ ≤ M / (π · y), which tends to zero as y → ∞. -/
theorem D_tendsto_zero_of_isBoundedAtImInfty {f : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbdd : IsBoundedAtImInfty f) :
    Filter.Tendsto (D f) atImInfty (nhds 0) := by
  obtain ⟨M, A, hMA⟩ := isBoundedAtImInfty_iff.mp hbdd
  -- ‖D f z‖ ≤ M / (π · z.im) by Cauchy estimate; the bound → 0 since z.im → ∞.
  suffices h : ∀ᶠ z : ℍ in atImInfty, ‖D f z‖ ≤ M / (π * z.im) by
    apply squeeze_zero_norm' h
    have := Filter.tendsto_im_atImInfty.inv_tendsto_atTop.const_mul (M / π)
    simp only [Pi.inv_apply, mul_zero] at this
    exact this.congr fun z => by field_simp
  have h_sphere_bdd : ∀ z : ℍ, 2 * max A 0 + 1 ≤ z.im →
      ∀ w ∈ Metric.sphere (z : ℂ) (z.im / 2), ‖(f ∘ ofComplex) w‖ ≤ M := by
    intro z hz_ge w hw
    have hw_im_pos : 0 < w.im :=
      closedBall_center_subset_upperHalfPlane z (Metric.sphere_subset_closedBall hw)
    have hdist : dist w z = z.im / 2 := Metric.mem_sphere.mp hw
    have habs : |w.im - z.im| ≤ z.im / 2 := by
      calc |w.im - z.im| = |(w - z).im| := by simp [Complex.sub_im]
        _ ≤ ‖w - z‖ := abs_im_le_norm _
        _ = dist w z := (dist_eq_norm _ _).symm
        _ = z.im / 2 := hdist
    have hw_im_ge_A : A ≤ w.im := by linarith [(abs_le.mp habs).1, le_max_left A 0]
    simpa [ofComplex_apply_of_im_pos hw_im_pos] using hMA ⟨w, hw_im_pos⟩ hw_im_ge_A
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨{z : ℍ | 2 * max A 0 + 1 ≤ z.im},
    (atImInfty_mem _).mpr ⟨_, fun _ h => h⟩, fun z hz => ?_⟩
  calc ‖D f z‖
      ≤ M / (2 * π * (z.im / 2)) := norm_D_le_of_sphere_bound (by linarith [z.im_pos])
          (diffContOnCl_comp_ofComplex_of_mdifferentiable hf
            (closedBall_center_subset_upperHalfPlane z)) (h_sphere_bdd z hz)
    _ = M / (π * z.im) := by ring


-- TODO: The following lemma from Gauss overlaps with `D_tendsto_zero_of_isBoundedAtImInfty`
-- above. We will probably want to drop it.
/-- The D-derivative tends to 0 at infinity for bounded holomorphic functions. -/
public lemma D_isZeroAtImInfty_of_bounded {f : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbdd : IsBoundedAtImInfty f) :
    IsZeroAtImInfty (D f) := by
  rw [UpperHalfPlane.isZeroAtImInfty_iff]
  intro ε hε
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at hbdd
  obtain ⟨M, A, hMA⟩ := hbdd
  refine ⟨max (2 * max A 0 + 1) (M / (Real.pi * ε)), fun z hz => ?_⟩
  have hz' : 2 * max A 0 + 1 ≤ z.im := le_trans (le_max_left _ _) hz
  have hz_im : M / (Real.pi * ε) ≤ z.im := le_trans (le_max_right _ _) hz
  have hpiε : 0 < (Real.pi * ε) := mul_pos Real.pi_pos hε
  have hpiIm : 0 < (Real.pi * z.im) := mul_pos Real.pi_pos z.im_pos
  have hMle : M ≤ ε * (Real.pi * z.im) := by
    have hMle' : M ≤ z.im * (Real.pi * ε) := (div_le_iff₀ hpiε).1 hz_im
    simpa [mul_assoc, mul_left_comm, mul_comm] using hMle'
  have hbound : M / (π * z.im) ≤ ε :=
    (div_le_iff₀ hpiIm).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hMle)
  exact (norm_D_le_div_pi_im_of_bounded hf hMA hz').trans hbound
