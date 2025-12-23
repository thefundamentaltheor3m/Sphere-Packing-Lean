import SpherePacking.ModularForms.Eisenstein
import SpherePacking.ModularForms.tsumderivWithin
import Mathlib.Analysis.Calculus.DerivativeTest

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap

open scoped ModularForm MatrixGroups Manifold

/-!
Definition of (Serre) derivative of modular forms.
Prove Ramanujan's formulas on derivatives of Eisenstein series.
-/

noncomputable def D (F : ℍ → ℂ) : ℍ → ℂ :=
  fun (z : ℍ) => (2 * π * I)⁻¹ * ((deriv (F ∘ ofComplex)) z)

/--
TODO: Remove this or move this to somewhere more appropriate.
-/
lemma MDifferentiableAt_DifferentiableAt {F : ℍ → ℂ} {z : ℍ}
  (h : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F z) :
  DifferentiableAt ℂ (F ∘ ofComplex) ↑z := by
  have h₁ : DifferentiableWithinAt ℂ (F ∘ ofComplex) Set.univ ↑z :=
    by simpa [writtenInExtChartAt, extChartAt, Set.range_id] using
      MDifferentiableWithinAt.differentiableWithinAt_writtenInExtChartAt h
  exact (differentiableWithinAt_univ.1 h₁)

/--
The converse direction: `DifferentiableAt` on ℂ implies `MDifferentiableAt` on ℍ.
-/
lemma DifferentiableAt_MDifferentiableAt {G : ℂ → ℂ} {z : ℍ}
    (h : DifferentiableAt ℂ G ↑z) : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (G ∘ (↑) : ℍ → ℂ) z := by
  rw [mdifferentiableAt_iff]
  -- Goal: DifferentiableAt ℂ ((G ∘ (↑)) ∘ ofComplex) ↑z
  -- The functions ((G ∘ (↑)) ∘ ofComplex) and G agree on the upper half-plane
  -- which is a neighborhood of ↑z
  apply DifferentiableAt.congr_of_eventuallyEq h
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw]
  exact congrArg G (UpperHalfPlane.coe_mk w hw)

/--
The derivative operator `D` preserves MDifferentiability.
If `F : ℍ → ℂ` is MDifferentiable, then `D F` is also MDifferentiable.
-/
theorem D_differentiable {F : ℍ → ℂ} (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (D F) := fun z =>
  let hDiffOn : DifferentiableOn ℂ (F ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    fun w hw => (MDifferentiableAt_DifferentiableAt (hF ⟨w, hw⟩)).differentiableWithinAt
  MDifferentiableAt.mul mdifferentiableAt_const <| DifferentiableAt_MDifferentiableAt <|
    (hDiffOn.deriv isOpen_upperHalfPlaneSet).differentiableAt
      (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)

/--
TODO: Move this to E2.lean.

NOTE: Proof available in PR #213 (gauss-math-inc) using eta function logDeriv.
This PR should wait for #213 to merge first.
-/
theorem E₂_holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) E₂ := sorry

/--
Basic properties of derivatives: linearity, Leibniz rule, etc.
-/
@[simp]
theorem D_add (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) :
    D (F + G) = D F + D G := by
  ext z
  have h : deriv ((F ∘ ofComplex) + (G ∘ ofComplex)) z
      = deriv (F ∘ ofComplex) z + deriv (G ∘ ofComplex) z := by
    refine deriv_add ?_ ?_
    · exact MDifferentiableAt_DifferentiableAt (hF z)
    · exact MDifferentiableAt_DifferentiableAt (hG z)
  calc
    D (F + G) z
    _ = (2 * π * I)⁻¹ * deriv ((F ∘ ofComplex) + (G ∘ ofComplex)) z := by rfl
    _ = (2 * π * I)⁻¹ * (deriv (F ∘ ofComplex) z + deriv (G ∘ ofComplex) z)
      := by rw [h]
    _ = (2 * π * I)⁻¹ * deriv (F ∘ ofComplex) z
        + (2 * π * I)⁻¹ * deriv (G ∘ ofComplex) z
      := by simp [mul_add]
    _ = D F z + D G z := by rfl

@[simp]
theorem D_sub (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    : D (F - G) = D F - D G := by
  ext z
  have h : deriv ((F ∘ ofComplex) - (G ∘ ofComplex)) z
      = deriv (F ∘ ofComplex) z - deriv (G ∘ ofComplex) z := by
    refine deriv_sub ?_ ?_
    · exact MDifferentiableAt_DifferentiableAt (hF z)
    · exact MDifferentiableAt_DifferentiableAt (hG z)
  calc
    D (F - G) z
    _ = (2 * π * I)⁻¹ * deriv ((F ∘ ofComplex) - (G ∘ ofComplex)) z := by rfl
    _ = (2 * π * I)⁻¹ * (deriv (F ∘ ofComplex) z - deriv (G ∘ ofComplex) z)
      := by rw [h]
    _ = (2 * π * I)⁻¹ * deriv (F ∘ ofComplex) z
        - (2 * π * I)⁻¹ * deriv (G ∘ ofComplex) z
      := by ring_nf
    _ = D F z - D G z := by rfl

@[simp]
theorem D_smul (c : ℂ) (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    : D (c • F) = c • D F := by
  ext z
  have h : deriv (c • (F ∘ ofComplex)) z = c • deriv (F ∘ ofComplex) z :=
    deriv_const_mul c (MDifferentiableAt_DifferentiableAt (hF z))
  calc
    D (c • F) z
    _ = (2 * π * I)⁻¹ * deriv (c • (F ∘ ofComplex)) z := by rfl
    _ = (2 * π * I)⁻¹ * (c * deriv (F ∘ ofComplex) z) := by rw [h, smul_eq_mul]
    _ = c * ((2 * π * I)⁻¹ * deriv (F ∘ ofComplex) z) := by ring_nf
    _ = c * D F z := by rfl

@[simp]
theorem D_mul (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    : D (F * G) = F * D G + D F * G := by
  ext z
  have h : deriv ((F ∘ ofComplex) * (G ∘ ofComplex)) z =
      F z * deriv (G ∘ ofComplex) z + deriv (F ∘ ofComplex) z * G z:= by
    have hFz := MDifferentiableAt_DifferentiableAt (hF z)
    have hGz := MDifferentiableAt_DifferentiableAt (hG z)
    rw [deriv_mul hFz hGz]
    simp only [Function.comp_apply, ofComplex_apply]
    group
  calc
    D (F * G) z
    _ = (2 * π * I)⁻¹ * deriv (F ∘ ofComplex * G ∘ ofComplex) z := by rfl
    _ = (2 * π * I)⁻¹ * (F z * deriv (G ∘ ofComplex) z + deriv (F ∘ ofComplex) z * G z)
      := by rw [h]
    _ = F z * ((2 * π * I)⁻¹ * deriv (G ∘ ofComplex) z) +
        (2 * π * I)⁻¹ * deriv (F ∘ ofComplex) z * G z
      := by ring_nf
    _ = F z * D G z + D F z * G z := by rfl

@[simp]
theorem D_sq (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    D (F ^ 2) = 2 * F * D F := by
  calc
    D (F ^ 2) = D (F * F) := by rw [pow_two]
    _ = F * D F + D F * F := by rw [D_mul F F hF hF]
    _ = 2 * F * D F := by ring_nf

@[simp]
theorem D_cube (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    D (F ^ 3) = 3 * F ^ 2 * D F := by
  have hF2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F ^ 2) := by rw [pow_two]; exact MDifferentiable.mul hF hF
  calc
    D (F ^ 3) = D (F * F ^ 2) := by ring_nf
    _ = F * D (F ^ 2) + D F * F ^ 2 := by rw [D_mul F (F ^ 2) hF hF2]
    _ = F * (2 * F * D F) + D F * F ^ 2 := by rw [D_sq F hF]
    _ = 3 * F^2 * D F := by ring_nf

@[simp]
theorem D_const (c : ℂ) (z : ℍ) : D (Function.const _ c) z = 0 := by
  have h : deriv (Function.const _ c ∘ ofComplex) z = 0 := by
    have h' : Function.const _ c ∘ ofComplex = Function.const _ c := by rfl
    rw [h']
    exact deriv_const _ c
  calc
    D (Function.const _ c) z
    _ = (2 * π * I)⁻¹ * deriv (Function.const _ c ∘ ofComplex) z := by rfl
    _ = (2 * π * I)⁻¹ * 0 := by rw [h]
    _ = 0 := by ring_nf


/--
Serre derivative of weight $k$.
Note that the definition makes sense for any analytic function $F : \mathbb{H} \to \mathbb{C}$.
-/
noncomputable def serre_D (k : ℂ) : (ℍ → ℂ) → (ℍ → ℂ) :=
  fun (F : ℍ → ℂ) => (fun z => D F z - k * 12⁻¹ * E₂ z * F z)

/--
Basic properties of Serre derivative: linearity, Leibniz rule, etc.
-/
theorem serre_D_add (k : ℤ) (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) : serre_D k (F + G) = serre_D k F + serre_D k G := by
  ext z
  simp only [serre_D, Pi.add_apply, D_add F G hF hG]
  ring_nf

theorem serre_D_smul (k : ℤ) (c : ℂ) (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (z : ℍ) :
    serre_D k (c • F) z = c * serre_D k F z := by
  simp only [serre_D, D_smul c F hF]
  simp
  ring_nf

theorem serre_D_mul (k₁ k₂ : ℤ) (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) (z : ℍ) :
    serre_D (k₁ + k₂) (F * G) z = F z * serre_D k₁ G z + G z * serre_D k₂ F z := by
  simp only [serre_D, D_mul F G hF hG]
  simp
  ring_nf

/--
The Serre derivative preserves MDifferentiability.
If `F : ℍ → ℂ` is MDifferentiable, then `serre_D k F` is also MDifferentiable.
-/
theorem serre_D_differentiable {F : ℍ → ℂ} {k : ℂ}
    (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (serre_D k F) := by
  -- serre_D k F = D F - k * 12⁻¹ * E₂ * F
  have h_term : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => k * 12⁻¹ * E₂ z * F z) := by
    have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => (k * 12⁻¹) * (E₂ z * F z)) :=
      MDifferentiable.mul mdifferentiable_const (E₂_holo'.mul hF)
    convert h1 using 1; ext z; simp only [mul_assoc]
  exact (D_differentiable hF).sub h_term

/-! ### Helper lemmas for D_slash

These micro-lemmas compute derivatives of the components in the slash action formula.
-/

open ModularGroup in
/-- Derivative of the denominator function: d/dz[cz + d] = c. -/
lemma deriv_denom (γ : SL(2, ℤ)) (z : ℂ) :
    deriv (fun w => denom γ w) z = ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) := by
  -- denom γ w = (γ : GL) 1 0 * w + (γ : GL) 1 1
  -- The GL entries come from ℤ via ℤ → ℝ → GL
  have hc : (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) := by simp
  have hd : (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ) := by simp
  simp only [denom]
  have h : (fun w => (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) * w +
      (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ)) =
      (fun w => ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * w + ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ)) := by
    ext w; rw [hc, hd]
  rw [h, deriv_add_const, deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one]

open ModularGroup in
/-- Derivative of the numerator function: d/dz[az + b] = a. -/
lemma deriv_num (γ : SL(2, ℤ)) (z : ℂ) :
    deriv (fun w => num γ w) z = ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) := by
  have ha : (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) := by simp
  have hb : (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) := by simp
  simp only [num]
  have h : (fun w => (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) * w +
      (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ)) =
      (fun w => ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * w + ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ)) := by
    ext w; rw [ha, hb]
  rw [h, deriv_add_const, deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one]

open ModularGroup in
/-- Differentiability of denom. -/
lemma differentiableAt_denom (γ : SL(2, ℤ)) (z : ℂ) :
    DifferentiableAt ℂ (fun w => denom γ w) z := by
  simp only [denom]
  fun_prop

open ModularGroup in
/-- Differentiability of num. -/
lemma differentiableAt_num (γ : SL(2, ℤ)) (z : ℂ) :
    DifferentiableAt ℂ (fun w => num γ w) z := by
  simp only [num]
  fun_prop

open ModularGroup in
/-- Derivative of the Möbius transformation: d/dz[(az+b)/(cz+d)] = 1/(cz+d)².
This uses det(γ) = 1, so (a(cz+d) - c(az+b)) = ad - bc = 1. -/
lemma deriv_moebius (γ : SL(2, ℤ)) (z : ℂ) (hz : denom γ z ≠ 0) :
    deriv (fun w => num γ w / denom γ w) z = 1 / (denom γ z) ^ 2 := by
  have hdiff_num : DifferentiableAt ℂ (fun w => num γ w) z := differentiableAt_num γ z
  have hdiff_denom : DifferentiableAt ℂ (fun w => denom γ w) z := differentiableAt_denom γ z
  have hderiv : HasDerivAt (fun w => num γ w / denom γ w)
      ((deriv (fun w => num γ w) z * denom γ z - num γ z * deriv (fun w => denom γ w) z)
        / (denom γ z) ^ 2) z :=
    hdiff_num.hasDerivAt.div hdiff_denom.hasDerivAt hz
  rw [hderiv.deriv, deriv_num, deriv_denom]
  -- Use det γ = 1: γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1
  have hdet : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ)
      - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) = 1 := by
    simp only [← Int.cast_mul, ← Int.cast_sub]
    have hdet' := Matrix.SpecialLinearGroup.det_coe γ
    simp only [Matrix.det_fin_two] at hdet'
    norm_cast
  -- Normalize coercions between GL and Matrix ℤ
  have ha : (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) := by simp
  have hb : (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) := by simp
  have hc : (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) := by simp
  have hd' : (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ) := by simp
  simp only [num, denom, ha, hb, hc, hd']
  -- Goal: (a * (c*z+d) - (a*z+b) * c) / (c*z+d)^2 = 1 / (c*z+d)^2
  -- Numerator: a*(cz+d) - c*(az+b) = acz + ad - acz - bc = ad - bc = 1 (det)
  have hdenom_eq : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * z +
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ) = denom γ z := by simp only [denom, hc, hd']
  rw [hdenom_eq]
  have hdenom_sq_ne : (denom γ z) ^ 2 ≠ 0 := pow_ne_zero 2 hz
  rw [div_eq_div_iff hdenom_sq_ne hdenom_sq_ne, one_mul]
  -- Goal: (a * denom - (az+b) * c) * denom^2 = denom^2
  -- This is 1 * denom^2 = denom^2 if we can show numerator = 1
  have hnum_eq : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * denom γ z -
      (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * z + ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ)) *
        ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) = 1 := by
    simp only [denom, hc, hd']
    linear_combination hdet
  rw [hnum_eq, one_mul]

open ModularGroup in
/-- Derivative of denom^(-k): d/dz[(cz+d)^(-k)] = -k * c * (cz+d)^(-k-1). -/
lemma deriv_denom_zpow (γ : SL(2, ℤ)) (k : ℤ) (z : ℂ) (hz : denom γ z ≠ 0) :
    deriv (fun w => (denom γ w) ^ (-k)) z =
        (-k : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * (denom γ z) ^ (-k - 1) := by
  have hdiff : DifferentiableAt ℂ (fun w => denom γ w) z := differentiableAt_denom γ z
  -- Use chain rule: d/dz[f(z)^m] = m * f(z)^(m-1) * f'(z)
  have hderiv_zpow : HasDerivAt (fun w => w ^ (-k)) (((-k : ℤ) : ℂ) * (denom γ z) ^ (-k - 1))
      (denom γ z) := hasDerivAt_zpow (-k) (denom γ z) (Or.inl hz)
  have hderiv_denom : HasDerivAt (fun w => denom γ w)
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) z := by
    rw [← deriv_denom]
    exact hdiff.hasDerivAt
  -- Chain rule
  have hcomp := hderiv_zpow.comp z hderiv_denom
  -- The composition equals fun w => (denom γ w) ^ (-k)
  have heq : (fun w => w ^ (-k)) ∘ (fun w => denom γ w) = (fun w => (denom γ w) ^ (-k)) := by
    ext w; simp only [Function.comp_apply]
  rw [← heq, hcomp.deriv]
  simp only [Int.cast_neg]
  ring

/--
The derivative anomaly: how D interacts with the slash action.
This is the key computation for proving Serre derivative equivariance.
-/
lemma D_slash (k : ℤ) (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (γ : SL(2, ℤ)) :
    D (F ∣[k] γ) = (D F ∣[k + 2] γ) -
        (fun z : ℍ => (k : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) * (F ∣[k] γ) z) := by
  -- Strategy (all micro-lemmas proven above):
  -- 1. SL_slash_apply: (F ∣[k] γ) z = F(γ•z) * denom(γ,z)^(-k)
  -- 2. coe_smul_of_det_pos: (γ•z : ℂ) = num γ z / denom γ z (since det(SL₂) = 1 > 0)
  -- 3. Product rule: deriv[f*g] = f*deriv[g] + deriv[f]*g
  -- 4. Chain rule: deriv[F ∘ mobius] = deriv[F](mobius z) * deriv_moebius
  -- 5. deriv_moebius: d/dz[num/denom] = 1/denom² (uses det = 1)
  -- 6. deriv_denom_zpow: d/dz[denom^(-k)] = -k * c * denom^(-k-1)
  --
  -- Computation:
  -- D(F ∣[k] γ) z = (2πi)⁻¹ * deriv[(F ∣[k] γ) ∘ ofComplex] z
  --   = (2πi)⁻¹ * deriv[w ↦ F(mobius w) * denom(w)^(-k)] z
  --   = (2πi)⁻¹ * [F(mobius z) * (-k * c * denom^(-k-1)) + deriv[F](mobius z) * (1/denom²) * denom^(-k)]
  --   = -k*(2πi)⁻¹*(c/denom)*(F ∣[k] γ)(z) + (2πi)⁻¹*deriv[F](γ•z)*denom^(-k-2)
  --   = (D F ∣[k+2] γ)(z) - k*(2πi)⁻¹*(c/denom)*(F ∣[k] γ)(z)
  ext z
  unfold D
  simp only [Pi.sub_apply]
  -- Key facts about denom
  have hz_denom_ne : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  -- Coercion normalization
  have hc : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) =
      (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) := by simp
  -- The derivative computation on ℂ using Filter.EventuallyEq.deriv_eq
  -- (F ∣[k] γ) ∘ ofComplex agrees with F(num/denom) * denom^(-k) on ℍ
  have hcomp : deriv (((F ∣[k] γ)) ∘ ofComplex) z =
      deriv (fun w => (F ∘ ofComplex) (num γ w / denom γ w) * (denom γ w) ^ (-k)) z := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw]
    rw [ModularForm.SL_slash_apply (f := F) (k := k) γ ⟨w, hw⟩]
    -- Need: F (γ • ⟨w, hw⟩) * denom γ ⟨w, hw⟩ ^ (-k) = (F ∘ ofComplex) (num γ w / denom γ w) * denom γ w ^ (-k)
    -- Key: (γ • ⟨w, hw⟩ : ℂ) = num γ w / denom γ w and denom γ ⟨w, hw⟩ = denom γ w
    congr 1
    · -- F (γ • ⟨w, hw⟩) = (F ∘ ofComplex) (num γ w / denom γ w)
      -- Need: γ • ⟨w, hw⟩ = ofComplex (num γ w / denom γ w) as points in ℍ
      have hdet_pos : (0 : ℝ) < ((γ : GL (Fin 2) ℝ).det).val := by simp
      -- The smul result as element of ℍ, then coerce to ℂ
      let gz : ℍ := γ • ⟨w, hw⟩
      -- The key: (gz : ℂ) = num/denom (using the lemma for GL coercion)
      have hsmul_coe : (gz : ℂ) = num γ w / denom γ w := by
        have h := UpperHalfPlane.coe_smul_of_det_pos hdet_pos ⟨w, hw⟩
        simp only [gz] at h ⊢
        exact h
      -- im(num/denom) > 0 follows from gz ∈ ℍ
      have hmob_im : (num γ w / denom γ w).im > 0 := by
        rw [← hsmul_coe]; exact gz.im_pos
      -- Now F(gz) = F(ofComplex(num/denom)) = (F ∘ ofComplex)(num/denom)
      -- gz = γ • ⟨w, hw⟩, so F gz = F (γ • ⟨w, hw⟩)
      congr 1
      -- Show gz = ofComplex (num/denom) as points in ℍ
      apply Subtype.ext
      rw [ofComplex_apply_of_im_pos hmob_im]
      exact hsmul_coe
  rw [hcomp]
  -- Now apply product rule: deriv[f * g] = f * deriv[g] + deriv[f] * g
  -- where f(w) = (F ∘ ofComplex)(num w / denom w) and g(w) = denom(w)^(-k)
  --
  -- Setup differentiability for product rule
  have hdenom_ne : ∀ w : ℂ, w.im > 0 → denom γ w ≠ 0 := fun w hw =>
    UpperHalfPlane.denom_ne_zero γ ⟨w, hw⟩
  have hz_im_pos : (z : ℂ).im > 0 := z.im_pos
  have hdiff_denom_zpow : DifferentiableAt ℂ (fun w => (denom γ w) ^ (-k)) z := by
    apply DifferentiableAt.zpow (differentiableAt_denom γ z) (Or.inl (hdenom_ne z hz_im_pos))
  -- For the F ∘ (num/denom) term, we need differentiability of the Möbius and F
  have hdiff_mobius : DifferentiableAt ℂ (fun w => num γ w / denom γ w) z := by
    exact (differentiableAt_num γ z).div (differentiableAt_denom γ z) (hdenom_ne z hz_im_pos)
  -- The composition (F ∘ ofComplex) ∘ mobius is differentiable at z
  -- because mobius(z) is in ℍ and F is MDifferentiable
  have hmobius_in_H : (num γ z / denom γ z).im > 0 := by
    -- γ • z is in ℍ, and (γ • z : ℂ) = num/denom
    have hdet_pos : (0 : ℝ) < ((γ : GL (Fin 2) ℝ).det).val := by simp
    have hsmul := UpperHalfPlane.coe_smul_of_det_pos hdet_pos z
    rw [← hsmul]
    exact (γ • z).im_pos
  have hdiff_F_comp : DifferentiableAt ℂ (F ∘ ofComplex) (num γ z / denom γ z) :=
    MDifferentiableAt_DifferentiableAt (hF ⟨num γ z / denom γ z, hmobius_in_H⟩)
  have hdiff_F_mobius : DifferentiableAt ℂ (fun w => (F ∘ ofComplex) (num γ w / denom γ w)) z := by
    -- The composition (F ∘ ofComplex) ∘ (num/denom) : ℂ → ℂ
    have heq : (fun w => (F ∘ ofComplex) (num γ w / denom γ w)) =
        (F ∘ ofComplex) ∘ (fun w => num γ w / denom γ w) := rfl
    rw [heq]
    exact DifferentiableAt.comp (z : ℂ) hdiff_F_comp hdiff_mobius
  -- Apply product rule
  -- Note: need to show the functions are equal to use deriv_mul
  have hfun_eq : (fun w => (F ∘ ofComplex) (num γ w / denom γ w) * (denom γ w) ^ (-k)) =
      ((fun w => (F ∘ ofComplex) (num γ w / denom γ w)) * (fun w => (denom γ w) ^ (-k))) := rfl
  rw [hfun_eq]
  have hprod := deriv_mul hdiff_F_mobius hdiff_denom_zpow
  rw [hprod]
  -- Apply chain rule to (F ∘ ofComplex) ∘ mobius
  have hchain : deriv (fun w => (F ∘ ofComplex) (num γ w / denom γ w)) z =
      deriv (F ∘ ofComplex) (num γ z / denom γ z) * deriv (fun w => num γ w / denom γ w) z := by
    -- Chain rule: d/dx[f(g(x))] = f'(g(x)) * g'(x)
    have heq : (fun w => (F ∘ ofComplex) (num γ w / denom γ w)) =
        (F ∘ ofComplex) ∘ (fun w => num γ w / denom γ w) := rfl
    have hcomp := hdiff_F_comp.hasDerivAt.comp (z : ℂ) hdiff_mobius.hasDerivAt
    rw [heq, hcomp.deriv]
  -- Substitute the micro-lemmas
  have hderiv_mob := deriv_moebius γ z (hdenom_ne z hz_im_pos)
  have hderiv_zpow := deriv_denom_zpow γ k z (hdenom_ne z hz_im_pos)
  rw [hchain, hderiv_mob, hderiv_zpow]
  -- Now we have:
  -- (2πi)⁻¹ * [deriv(F∘ofComplex)(mob z) * (1/denom²) * denom^(-k) +
  --            (F∘ofComplex)(mob z) * (-k * c * denom^(-k-1))]
  -- = (D F ∣[k+2] γ) z - k * (2πi)⁻¹ * (c/denom) * (F ∣[k] γ) z
  --
  -- Key observations:
  -- - (2πi)⁻¹ * deriv(F∘ofComplex)(mob z) = D F (γ • z)  (by def of D)
  -- - denom^(-k) / denom² = denom^(-k-2)
  -- - (D F)(γ • z) * denom^(-k-2) = (D F ∣[k+2] γ) z
  -- - (F∘ofComplex)(mob z) * denom^(-k) = F(γ • z) * denom^(-k) = (F ∣[k] γ) z
  -- - -k * c * denom^(-k-1) * (2πi)⁻¹ = -k * (2πi)⁻¹ * c/denom * denom^(-k)
  --
  -- Relate mobius to γ • z
  have hdet_pos : (0 : ℝ) < ((γ : GL (Fin 2) ℝ).det).val := by simp
  -- The key: ↑(γ • z) = num/denom (explicit coercion from ℍ to ℂ)
  have hmob_eq : ↑(γ • z) = num γ z / denom γ z :=
    UpperHalfPlane.coe_smul_of_det_pos hdet_pos z
  -- Relate (F ∘ ofComplex)(mob z) to F(γ • z)
  have hF_mob : (F ∘ ofComplex) (num γ z / denom γ z) = F (γ • z) := by
    simp only [Function.comp_apply, ← hmob_eq, ofComplex_apply]
  -- Relate deriv(F∘ofComplex) to D via (2πi)⁻¹
  have hD_eq : (2 * π * I)⁻¹ * deriv (F ∘ ofComplex) (num γ z / denom γ z) = D F (γ • z) := by
    unfold D
    congr 1
    rw [← hmob_eq]
  -- The slash action values
  have hslash_k : (F ∣[k] γ) z = F (γ • z) * (denom γ z) ^ (-k) := by
    rw [ModularForm.SL_slash_apply (f := F) (k := k) γ z]
  have hslash_k2 : (D F ∣[k + 2] γ) z = D F (γ • z) * (denom γ z) ^ (-(k + 2)) := by
    rw [ModularForm.SL_slash_apply (f := D F) (k := k + 2) γ z]
  -- Final algebraic manipulation combining all lemmas
  -- Goal: (2πi)⁻¹ * (deriv(F∘ofComplex)(mob z) * (1/denom²) * denom^(-k) +
  --                   (F∘ofComplex)(mob z) * (-k * c * denom^(-k-1)))
  --      = D F(γ•z) * denom^(-(k+2)) - k * (2πi)⁻¹ * (c/denom) * F(γ•z) * denom^(-k)
  -- This follows from the above lemmas by algebraic manipulation
  --
  -- First expand the slash action on the RHS and normalize denom coercions
  simp only [ModularForm.SL_slash_apply, hF_mob, hmob_eq]
  -- Now both sides should have normalized denom (num/denom arguments and ℂ coercions)
  -- Key identities for zpow:
  -- (1/denom²) * denom^(-k) = denom^(-2) * denom^(-k) = denom^(-k-2) = denom^(-(k+2))
  -- -k * c * denom^(-k-1) = -k * (c/denom) * denom^(-k)
  --
  -- Use zpow identities
  have hpow_combine : 1 / (denom γ z) ^ 2 * (denom γ z) ^ (-k) = (denom γ z) ^ (-(k + 2)) := by
    rw [one_div, ← zpow_natCast (denom γ z) 2, ← zpow_neg, ← zpow_add₀ hz_denom_ne]
    congr 1
    ring
  have hpow_m1 : (denom γ z) ^ (-k - 1) = (denom γ z) ^ (-1 : ℤ) * (denom γ z) ^ (-k) := by
    rw [← zpow_add₀ hz_denom_ne]
    congr 1
    ring
  -- Rewrite powers on LHS
  conv_lhs =>
    rw [mul_assoc (deriv (F ∘ ofComplex) (num γ z / denom γ z)) (1 / denom γ z ^ 2) _]
    rw [hpow_combine, hpow_m1]
  -- Now the goal should be cleaner - distribute and simplify
  simp only [zpow_neg_one]
  ring

/--
E₂ transformation under slash action, derived from G₂_transform.
E₂ = G₂ / (2*ζ(2)), and G₂ ∣[2] γ = G₂ - D₂ γ.
-/
lemma E₂_slash_transform (γ : SL(2, ℤ)) :
    E₂ ∣[(2 : ℤ)] γ = E₂ - (1 / (2 * riemannZeta 2)) • D₂ γ := by
  -- Use G₂_transform and E₂ = (1/(2*ζ(2))) • G₂
  have hG := G₂_transform γ
  rw [E₂]
  -- E₂ ∣[2] γ = (1/(2ζ(2)) • G₂) ∣[2] γ = 1/(2ζ(2)) • (G₂ ∣[2] γ)
  rw [ModularForm.SL_smul_slash (2 : ℤ) γ G₂ (1 / (2 * riemannZeta 2))]
  rw [hG]
  ext z
  simp only [one_div, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- Helper lemma: The anomaly coefficient vanishes.
The key identity is: (1/12) * (1/(2ζ(2))) * 2πi + (2πi)⁻¹ = 0
Using ζ(2) = π²/6, this becomes: i/(2π) + 1/(2πi) = i/(2π) - i/(2π) = 0 -/
lemma anomaly_coeff_zero : (12 : ℂ)⁻¹ * (2 * riemannZeta 2)⁻¹ * (2 * π * I) + (2 * π * I)⁻¹ = 0 := by
  rw [riemannZeta_two]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have h6 : (6 : ℂ) ≠ 0 := by norm_num
  have h12 : (12 : ℂ) ≠ 0 := by norm_num
  field_simp
  ring_nf
  -- Goal: 12 + I ^ 2 * 12 = 0, which is 12 + (-1) * 12 = 0 since I^2 = -1
  simp only [I_sq, neg_one_mul, add_neg_cancel]

/--
Serre derivative is equivariant under the slash action. More precisely, if `F` is invariant
under the slash action of weight `k`, then `serre_D k F` is invariant under the slash action
of weight `k + 2`.
-/
theorem serre_D_slash_equivariant (k : ℤ) (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    ∀ γ : SL(2, ℤ), serre_D k F ∣[k + 2] γ = serre_D k (F ∣[k] γ) := by
  intro γ
  ext z
  -- Get key transformations
  have hDslash := congrFun (D_slash k F hF γ) z
  simp only [Pi.sub_apply] at hDslash
  have hE₂slash := congrFun (E₂_slash_transform γ) z
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hE₂slash
  -- Product slash: (E₂ * F) ∣[k+2] γ = (E₂ ∣[2] γ) * (F ∣[k] γ)
  have hmul : ((E₂ * F) ∣[k + 2] γ) z = (E₂ ∣[(2 : ℤ)] γ) z * (F ∣[k] γ) z := by
    have h := congrFun (ModularForm.mul_slash_SL2 (2 : ℤ) k γ E₂ F) z
    simp only [Pi.mul_apply] at h; convert h using 2; ring
  -- D₂ in terms of c/denom
  have hD₂ : D₂ γ z = (2 * π * I) * (↑(γ 1 0) / denom γ z) := by
    simp only [D₂]
    ring
  -- LHS: (serre_D k F ∣[k+2] γ) z = (D F - (k/12) * E₂ * F) ∣[k+2] γ
  -- By linearity of slash: = D F ∣[k+2] γ - (k/12) * (E₂ * F) ∣[k+2] γ
  have hLHS : (serre_D k F ∣[k + 2] γ) z =
      (D F ∣[k + 2] γ) z - (k : ℂ) * (12 : ℂ)⁻¹ * ((E₂ * F) ∣[k + 2] γ) z := by
    simp only [serre_D, ModularForm.SL_slash_apply, Pi.mul_apply]
    ring
  -- RHS: serre_D k (F ∣[k] γ) z = D (F ∣[k] γ) z - (k/12) * E₂ z * (F ∣[k] γ) z
  have hRHS : serre_D k (F ∣[k] γ) z =
      D (F ∣[k] γ) z - (k : ℂ) * (12 : ℂ)⁻¹ * E₂ z * (F ∣[k] γ) z := by
    simp only [serre_D]
  -- Substitute hLHS and hRHS pattern and perform calc
  rw [hLHS, hRHS]
  rw [hmul, hE₂slash, hD₂]
  -- From D_slash: D (F ∣[k] γ) z = (D F ∣[k + 2] γ) z - k*(2πi)⁻¹*(c/denom)*(F ∣[k] γ) z
  -- Rearranging: (D F ∣[k + 2] γ) z = D (F ∣[k] γ) z + k*(2πi)⁻¹*(c/denom)*(F ∣[k] γ) z
  have hDslash' : (D F ∣[k + 2] γ) z = D (F ∣[k] γ) z +
      (k : ℂ) * (2 * π * I)⁻¹ * (↑(γ 1 0) / denom γ z) * (F ∣[k] γ) z := by
    -- hDslash: D (F ∣[k] γ) z = (D F ∣[k + 2] γ) z - X where X = k*(2πi)⁻¹*(c/denom)*(F ∣[k] γ) z
    -- So: (D F ∣[k + 2] γ) z = D (F ∣[k] γ) z + X
    calc (D F ∣[k + 2] γ) z
        = (D F ∣[k + 2] γ) z - (k : ℂ) * (2 * π * I)⁻¹ * (↑(γ 1 0) / denom γ z) * (F ∣[k] γ) z
          + (k : ℂ) * (2 * π * I)⁻¹ * (↑(γ 1 0) / denom γ z) * (F ∣[k] γ) z := by ring
      _ = D (F ∣[k] γ) z + (k : ℂ) * (2 * π * I)⁻¹ * (↑(γ 1 0) / denom γ z) * (F ∣[k] γ) z := by
          rw [← hDslash]
  rw [hDslash']
  -- Now the goal is pure algebra:
  -- D(F∣γ) + k*(2πi)⁻¹*(c/denom)*F∣γ - k/12*(E₂ - (2ζ(2))⁻¹*2πi*(c/denom))*F∣γ
  -- = D(F∣γ) - k/12*E₂*F∣γ
  -- Expanding: D(F∣γ) + k*(2πi)⁻¹*X - k/12*E₂*F∣γ + k/12*(2ζ(2))⁻¹*2πi*X
  -- = D(F∣γ) - k/12*E₂*F∣γ
  -- where X = (c/denom)*F∣γ
  -- So we need: k*(2πi)⁻¹*X + k/12*(2ζ(2))⁻¹*2πi*X = 0
  -- Factor: k*X*[(2πi)⁻¹ + (12)⁻¹*(2ζ(2))⁻¹*2πi] = 0
  -- This is anomaly_coeff_zero!
  have h_cancel := anomaly_coeff_zero
  have h_factored : ∀ (x : ℂ), (12 : ℂ)⁻¹ * (2 * riemannZeta 2)⁻¹ * (2 * π * I) * x +
      (2 * π * I)⁻¹ * x = 0 := fun x => by
    calc (12 : ℂ)⁻¹ * (2 * riemannZeta 2)⁻¹ * (2 * π * I) * x + (2 * π * I)⁻¹ * x
        = ((12 : ℂ)⁻¹ * (2 * riemannZeta 2)⁻¹ * (2 * π * I) + (2 * π * I)⁻¹) * x := by ring
      _ = 0 * x := by rw [h_cancel]
      _ = 0 := by ring
  -- Use abbreviations for readability
  set D' := D (F ∣[k] γ) z with hD'
  set c_div_d := (↑(γ 1 0) : ℂ) / denom γ z with hcd
  set F' := (F ∣[k] γ) z with hF'
  set π2I := (2 * π * I : ℂ) with hπ2I
  set ζ2 := riemannZeta 2 with hζ2
  -- h_factored using abbreviations
  have h_app : (12 : ℂ)⁻¹ * (2 * ζ2)⁻¹ * π2I * ((k : ℂ) * c_div_d * F') +
      π2I⁻¹ * ((k : ℂ) * c_div_d * F') = 0 := h_factored ((k : ℂ) * c_div_d * F')
  -- Goal: D' + k*π2I⁻¹*c_div_d*F' - k/12*(E₂ z - (2ζ2)⁻¹*π2I*c_div_d)*F'
  --     = D' - k/12*E₂ z*F'
  -- Expanding and rearranging:
  -- need k*π2I⁻¹*c_div_d*F' + k/12*(2ζ2)⁻¹*π2I*c_div_d*F' = 0
  -- = k * c_div_d * F' * (π2I⁻¹ + 12⁻¹*(2ζ2)⁻¹*π2I)
  -- = 0 by h_app
  ring_nf
  -- h_goal: the anomaly terms sum to 0
  have h_goal : (k : ℂ) * π2I * c_div_d * F' * ζ2⁻¹ * (1 / 24) + (k : ℂ) * π2I⁻¹ * c_div_d * F' = 0 := by
    calc (k : ℂ) * π2I * c_div_d * F' * ζ2⁻¹ * (1 / 24) + (k : ℂ) * π2I⁻¹ * c_div_d * F'
        = (12 : ℂ)⁻¹ * (2 * ζ2)⁻¹ * π2I * ((k : ℂ) * c_div_d * F') +
          π2I⁻¹ * ((k : ℂ) * c_div_d * F') := by ring
      _ = 0 := h_app
  calc D' + ↑k * π2I * c_div_d * F' * ζ2⁻¹ * (1 / 24) + ↑k * π2I⁻¹ * c_div_d * F' +
      ↑k * F' * E₂ z * (-1 / 12)
    _ = D' + ↑k * F' * E₂ z * (-1 / 12) +
        ((k : ℂ) * π2I * c_div_d * F' * ζ2⁻¹ * (1 / 24) + (k : ℂ) * π2I⁻¹ * c_div_d * F') := by ring
    _ = D' + ↑k * F' * E₂ z * (-1 / 12) + 0 := by rw [h_goal]
    _ = D' + ↑k * F' * E₂ z * (-1 / 12) := by ring

theorem serre_D_slash_invariant (k : ℤ) (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (γ : SL(2, ℤ)) (h : F ∣[k] γ = F) :
    serre_D k F ∣[k + 2] γ = serre_D k F := by
  rw [serre_D_slash_equivariant, h]
  exact hF

/-! ### Bounded at infinity lemmas for Ramanujan's identities

These lemmas establish that `serre_D 4 E₄` is bounded at cusps, which is needed
to apply the dimension formula for weight-6 modular forms.
-/

/-- E₂ is bounded at infinity.

Uses `E₂_eq`: E₂(z) = 1 - 24·Σn·qⁿ/(1-qⁿ) where q = exp(2πiz).
As im(z) → ∞, ‖q‖ → 0, so the sum → 0, hence E₂(z) → 1.

**Proof strategy** (partially implemented below):
1. For im(z) ≥ 1, |q| ≤ exp(-2π) < 0.002
2. Bound: |n·q^n/(1-q^n)| ≤ n·|q|^n/(1-|q|) since |1-q^n| ≥ 1-|q| for n ≥ 1
3. The tsum is bounded by |q|/(1-|q|)³ < 0.003
4. Therefore |E₂| ≤ 1 + 24·0.003 < 2

**Remaining**: Complete the tsum bound using `norm_tsum_le_tsum_norm` and
geometric series. See JacobiTheta.lean:374 (`isBoundedAtImInfty_H₂`) for similar proofs. -/
lemma E₂_isBoundedAtImInfty : IsBoundedAtImInfty E₂ := by
  -- Use E₂_eq: E₂ z = 1 - 24 * ∑' n : ℕ+, n * q^n / (1 - q^n) where q = exp(2πiz)
  -- As im(z) → ∞, |q| → 0, so the sum → 0, hence E₂ → 1 (bounded).
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  -- We'll show: ∃ M A : ℝ, ∀ z : ℍ, A ≤ im z → ‖E₂ z‖ ≤ M
  -- Use explicit constant to avoid numeric grind: M = 1 + 24 * exp(-2π) / (1 - exp(-2π))³
  set r₀ : ℝ := Real.exp (-2 * π) with hr₀_def
  refine ⟨1 + 24 * (r₀ / (1 - r₀) ^ 3), 1, ?_⟩
  intro z hz
  rw [E₂_eq]
  -- E₂ z = 1 - 24 * ∑' n, n * q^n / (1 - q^n)
  -- Need to bound ‖1 - 24 * tsum‖ ≤ 1 + 24 * ‖tsum‖
  have hq : ‖cexp (2 * π * Complex.I * z)‖ < 1 := norm_exp_two_pi_I_lt_one z
  -- When im(z) ≥ 1, |q| ≤ exp(-2π) < 0.002, so the sum is very small
  have hq_bound : ‖cexp (2 * π * Complex.I * z)‖ ≤ Real.exp (-2 * π) := by
    have h1 : (2 * ↑π * Complex.I * (z : ℂ)).re = -2 * π * z.im := by
      rw [show (2 : ℂ) * ↑π * Complex.I * z = Complex.I * (2 * π * z) by ring]
      simp [Complex.I_re, Complex.I_im, mul_comm]
    rw [Complex.norm_exp, h1, Real.exp_le_exp]
    have hpi : 0 < π := Real.pi_pos
    have him : 1 ≤ z.im := hz
    nlinarith
  -- Step 1: Triangle inequality: ‖1 - 24 * tsum‖ ≤ 1 + 24 * ‖tsum‖
  calc ‖1 - 24 * ∑' (n : ℕ+), ↑n * cexp (2 * π * Complex.I * ↑n * ↑z) /
          (1 - cexp (2 * π * Complex.I * ↑n * ↑z))‖
      ≤ ‖(1 : ℂ)‖ + ‖24 * ∑' (n : ℕ+), ↑n * cexp (2 * π * Complex.I * ↑n * ↑z) /
          (1 - cexp (2 * π * Complex.I * ↑n * ↑z))‖ := norm_sub_le _ _
    _ = 1 + 24 * ‖∑' (n : ℕ+), ↑n * cexp (2 * π * Complex.I * ↑n * ↑z) /
          (1 - cexp (2 * π * Complex.I * ↑n * ↑z))‖ := by
        simp only [norm_one, norm_mul, RCLike.norm_ofNat]
    _ ≤ 1 + 24 * (r₀ / (1 - r₀) ^ 3) := ?_
  -- Step 2: Need to show ‖tsum‖ ≤ r₀ / (1 - r₀)³ where r₀ = exp(-2π)
  -- Strategy: Use norm_tsum_le_tsum_norm + term bound + geometric series
  -- Let q = exp(2πiz). We need to bound the tsum.
  set q : ℂ := cexp (2 * π * Complex.I * z) with hq_def
  -- Rewrite the sum in terms of q: exp(2πinz) = (exp(2πiz))^n = q^n
  have hexp_pow : ∀ n : ℕ, cexp (2 * π * Complex.I * n * z) = q ^ n := fun n => by
    rw [hq_def, ← Complex.exp_nat_mul]
    congr 1
    ring
  have hsum_eq : (fun n : ℕ+ => ↑n * cexp (2 * π * Complex.I * ↑n * ↑z) /
      (1 - cexp (2 * π * Complex.I * ↑n * ↑z))) =
      (fun n : ℕ+ => ↑n * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))) := by
    ext n
    simp only [hexp_pow]
  rw [hsum_eq]
  -- Key bounds on r₀
  have hr₀_pos : 0 < r₀ := Real.exp_pos _
  have hr₀_lt_one : r₀ < 1 := by
    simp only [hr₀_def]
    have hpi : 0 < π := Real.pi_pos
    calc Real.exp (-2 * π) < Real.exp 0 := Real.exp_strictMono (by linarith)
      _ = 1 := Real.exp_zero
  have hone_sub_r₀_pos : 0 < 1 - r₀ := by linarith
  -- Key bounds on q
  have hq_lt_one : ‖q‖ < 1 := hq
  have hq_pos : 0 < ‖q‖ := norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hone_sub_q_pos : 0 < 1 - ‖q‖ := by linarith
  -- Term bound: ‖n * q^n / (1 - q^n)‖ ≤ n * ‖q‖^n / (1 - ‖q‖)
  have hterm_bound : ∀ n : ℕ+, ‖(n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ ≤
      n * ‖q‖ ^ (n : ℕ) / (1 - ‖q‖) := fun n => by
    have hqn_lt : ‖q ^ (n : ℕ)‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq_lt_one n.ne_zero
    have hdenom_ne : 1 - q ^ (n : ℕ) ≠ 0 := by
      intro h; simp only [sub_eq_zero] at h
      have : ‖q ^ (n : ℕ)‖ = 1 := by rw [← h]; exact norm_one
      linarith
    rw [norm_div, norm_mul, Complex.norm_natCast]
    -- |1 - q^n| ≥ 1 - |q^n| ≥ 1 - |q| (reverse triangle inequality)
    have hdenom_lower : 1 - ‖q‖ ≤ ‖1 - q ^ (n : ℕ)‖ := by
      have h1 : 1 - ‖q ^ (n : ℕ)‖ ≤ ‖1 - q ^ (n : ℕ)‖ := by
        have := norm_sub_norm_le (1 : ℂ) (q ^ (n : ℕ))
        simp only [norm_one] at this
        linarith
      have h2 : ‖q‖ ^ (n : ℕ) ≤ ‖q‖ := by
        have := pow_le_pow_of_le_one (norm_nonneg _) hq_lt_one.le n.one_le
        simp at this; exact this
      calc 1 - ‖q‖ ≤ 1 - ‖q‖ ^ (n : ℕ) := by linarith
        _ = 1 - ‖q ^ (n : ℕ)‖ := by rw [norm_pow]
        _ ≤ _ := h1
    -- Now: (n * |q|^n) / |1 - q^n| ≤ (n * |q|^n) / (1 - |q|)
    calc ↑n * ‖q ^ (n : ℕ)‖ / ‖1 - q ^ (n : ℕ)‖
        ≤ ↑n * ‖q ^ (n : ℕ)‖ / (1 - ‖q‖) := by
          apply div_le_div_of_nonneg_left _ hone_sub_q_pos hdenom_lower
          exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
      _ = ↑n * ‖q‖ ^ (n : ℕ) / (1 - ‖q‖) := by rw [norm_pow]
  -- Set r = ‖q‖ for convenience
  set r : ℝ := ‖q‖ with hr_def
  have hr_pos : 0 < r := hq_pos
  have hr_lt_one : r < 1 := hq_lt_one
  have hr_le_r₀ : r ≤ r₀ := hq_bound
  have hone_sub_r_pos : 0 < 1 - r := hone_sub_q_pos
  have hr_norm_lt_one : ‖r‖ < 1 := by
    simp only [Real.norm_eq_abs, abs_of_nonneg hr_pos.le, hr_lt_one]
  -- Summability of n * r^n on ℕ (from mathlib)
  have hsumm_nat : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    have := summable_pow_mul_geometric_of_norm_lt_one 1 hr_norm_lt_one
    simp only [pow_one] at this
    exact this
  -- Convert to ℕ+ via nat_pos_tsum2 (using f 0 = 0)
  have hsumm_pnat : Summable (fun n : ℕ+ => (n : ℝ) * r ^ (n : ℕ)) := by
    have h0 : (fun n : ℕ => (n : ℝ) * r ^ n) 0 = 0 := by simp
    exact (nat_pos_tsum2 _ h0).mpr hsumm_nat
  -- Summability with (1 - r)⁻¹ factor
  have hsumm_majorant : Summable (fun n : ℕ+ => (n : ℝ) * r ^ (n : ℕ) / (1 - r)) := by
    have hr_ne : (1 - r) ≠ 0 := hone_sub_r_pos.ne'
    simpa [div_eq_mul_inv] using hsumm_pnat.mul_right (1 - r)⁻¹
  -- Summability of the complex sum norms
  have hsumm_norms : Summable (fun n : ℕ+ => ‖(n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hsumm_majorant
    convert hterm_bound n using 2
  -- Bound: ‖tsum‖ ≤ ∑' (n : ℕ+), ‖term‖ ≤ ∑' (n : ℕ+), n * r^n / (1 - r)
  have htsum_le : ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ ≤
      ∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ) / (1 - r) := by
    calc ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖
        ≤ ∑' n : ℕ+, ‖(n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ :=
          norm_tsum_le_tsum_norm hsumm_norms
      _ ≤ ∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ) / (1 - r) :=
          Summable.tsum_le_tsum (fun n => by convert hterm_bound n using 2)
            hsumm_norms hsumm_majorant
  -- Compute ∑' n : ℕ, n * r^n = r / (1 - r)²
  have hsum_nat : (∑' n : ℕ, (n : ℝ) * r ^ n) = r / (1 - r) ^ 2 :=
    tsum_coe_mul_geometric_of_norm_lt_one hr_norm_lt_one
  -- Convert ℕ+ sum via tsum_pnat_eq_tsum_succ4 (f 0 = 0 so sums match)
  have hsum_pnat : (∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ)) = r / (1 - r) ^ 2 := by
    have heq := tsum_pnat_eq_tsum_succ4 (fun n => (n : ℝ) * r ^ n) hsumm_nat
    simp only [Nat.cast_zero, zero_mul, zero_add] at heq
    rw [← hsum_nat]; exact heq
  -- With (1-r)⁻¹ factor: r / (1-r)³
  have hsum_majorant_eq : (∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ) / (1 - r)) = r / (1 - r) ^ 3 := by
    have hr_ne : (1 - r) ≠ 0 := hone_sub_r_pos.ne'
    rw [tsum_div_const, hsum_pnat]
    field_simp
  -- Now: ‖tsum‖ ≤ r / (1-r)³ ≤ r₀ / (1-r₀)³
  -- Monotonicity: f(x) = x/(1-x)³ is increasing on [0,1) since f'(x) = (1+2x)/(1-x)⁴ > 0
  have hmono : r / (1 - r) ^ 3 ≤ r₀ / (1 - r₀) ^ 3 := by
    -- Since 0 ≤ r ≤ r₀ < 1, and x/(1-x)³ is increasing on [0,1)
    have h1 : 0 ≤ r := hr_pos.le
    have h2 : r ≤ r₀ := hr_le_r₀
    have h3 : r₀ < 1 := hr₀_lt_one
    -- Use gcongr for numerator and denominator separately
    gcongr
  -- Chain the bounds
  have htsum_bound : ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ ≤
      r₀ / (1 - r₀) ^ 3 := by
    calc ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖
        ≤ ∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ) / (1 - r) := htsum_le
      _ = r / (1 - r) ^ 3 := hsum_majorant_eq
      _ ≤ r₀ / (1 - r₀) ^ 3 := hmono
  -- Final: 24 * ‖tsum‖ ≤ 24 * r₀ / (1 - r₀)³
  gcongr

/-- E₄ is bounded at infinity (as a modular form). -/
lemma E₄_isBoundedAtImInfty : IsBoundedAtImInfty E₄.toFun :=
  ModularFormClass.bdd_at_infty E₄

/-- The product E₂ · E₄ is bounded at infinity. -/
lemma E₂_mul_E₄_isBoundedAtImInfty : IsBoundedAtImInfty (E₂ * E₄.toFun) := by
  exact E₂_isBoundedAtImInfty.mul E₄_isBoundedAtImInfty

/-- D E₄ is bounded at infinity.

The q-expansion D(E₄) = 240·Σn·σ₃(n)·qⁿ has no constant term, so D(E₄) → 0 as im(z) → ∞.
This is even stronger than boundedness: D(E₄) vanishes at infinity.

**Proof outline**: D commutes with the q-expansion tsum (by uniform convergence),
and D(qⁿ) = n·qⁿ for q = exp(2πiz) (up to normalizing constants).
Since the sum has no q⁰ term, it vanishes as ‖q‖ → 0.

**Blocker**: Need D-tsum interchange lemma. See Issue #90 for the q-expansion approach
to Ramanujan's identities. Could use `D_E4_qexp` once that's proved. -/
lemma D_E₄_isBoundedAtImInfty : IsBoundedAtImInfty (D E₄.toFun) := by
  sorry

/-- serre_D 4 E₄ is bounded at infinity. -/
lemma serre_D_E₄_isBoundedAtImInfty : IsBoundedAtImInfty (serre_D 4 E₄.toFun) := by
  -- serre_D 4 E₄ = D E₄ - (4/12)·E₂·E₄ = D E₄ - (1/3)·E₂·E₄
  -- Both terms are bounded at infinity
  unfold serre_D
  -- The subtraction of bounded functions is bounded
  have h1 : IsBoundedAtImInfty (D E₄.toFun) := D_E₄_isBoundedAtImInfty
  have h2 : IsBoundedAtImInfty (fun z => (4 : ℂ) * 12⁻¹ * E₂ z * E₄.toFun z) := by
    have hconst : IsBoundedAtImInfty (fun _ : ℍ => (4 : ℂ) * 12⁻¹) :=
      Filter.const_boundedAtFilter _ _
    convert hconst.mul E₂_mul_E₄_isBoundedAtImInfty using 1
    ext z
    simp only [Pi.mul_apply]
    ring
  exact h1.sub h2

/--
Serre derivative of Eisenstein series. Use `serre_D_slash_invariant` and compare constant terms.
Note that the dimensions of the spaces of modular forms are all 1.
-/
theorem ramanujan_E₂' : serre_D 1 E₂ = - 12⁻¹ * E₄.toFun := by sorry

/-- The Serre derivative of E₄ is a scalar multiple of E₆.
This uses the dimension formula: weight 6 modular forms are 1-dimensional, spanned by E₆.
The scalar is determined by comparing constant terms. -/
theorem ramanujan_E₄' : serre_D 4 E₄.toFun = - 3⁻¹ * E₆.toFun := by
  -- Strategy: Use the dimension argument.
  -- 1. serre_D 4 E₄ is weight-6 slash-invariant under Γ(1) (by serre_D_slash_invariant)
  -- 2. E₆ is weight-6 slash-invariant (it's a ModularForm Γ(1) 6)
  -- 3. Weight-6 modular forms are 1-dimensional (weight_six_one_dimensional)
  -- 4. The constant term of serre_D 4 E₄ is -1/3:
  --    - D(E₄) has constant term 0 (D kills constants, or equivalently, the q-expansion
  --      of D(E₄) = 240*∑n*σ₃(n)*q^n has no q^0 term)
  --    - E₂ has constant term 1, E₄ has constant term 1
  --    - serre_D 4 E₄ = D E₄ - (4/12) * E₂ * E₄ has constant term 0 - 1/3 * 1 = -1/3
  -- 5. E₆ has constant term 1, so -1/3 * E₆ has constant term -1/3
  -- 6. They match! And since weight-6 modular forms are spanned by E₆, we're done.
  --
  -- Technical note: To apply the dimension formula formally, we need to either:
  -- (a) Construct a ModularForm from serre_D 4 E₄ (requires bounded at cusps), or
  -- (b) Use q-expansion comparison directly
  --
  -- The bounded-at-cusps condition holds because:
  -- - D(E₄) vanishes at the cusp (no constant term in q-expansion)
  -- - E₂ * E₄ is bounded at the cusp (both have constant term 1)
  -- - So serre_D 4 E₄ → -1/3 at the cusp
  sorry

theorem ramanujan_E₆' : serre_D 6 E₆.toFun = - 2⁻¹ * E₄.toFun * E₄.toFun := by sorry

@[simp]
theorem ramanujan_E₂ : D E₂ = 12⁻¹ * (E₂ * E₂ - E₄.toFun) := by
  ext z
  have h := ramanujan_E₂'
  unfold serre_D at h
  have h1 := congrFun h z
  simp [field]
  field_simp at h1
  simpa [add_comm, sub_eq_iff_eq_add] using h1

@[simp]
theorem ramanujan_E₄ : D E₄.toFun = 3⁻¹ * (E₂ * E₄.toFun - E₆.toFun) := by
  ext z
  have h := ramanujan_E₄'
  unfold serre_D at h
  have h1 := congrFun h z
  simp [field]
  simp [field] at h1
  ring_nf
  ring_nf at h1
  have hc : (12 : ℂ) ≠ 0 := by norm_num
  apply (mul_right_inj' hc).mp
  ring_nf
  simpa [add_comm, sub_eq_iff_eq_add] using h1

@[simp]
theorem ramanujan_E₆ : D E₆.toFun = 2⁻¹ * (E₂ * E₆.toFun - E₄.toFun * E₄.toFun) := by
  ext z
  have h := ramanujan_E₆'
  unfold serre_D at h
  have h1 := congrFun h z
  simp [field]
  simp [field] at h1
  ring_nf
  ring_nf at h1
  have hc : (12 : ℂ) ≠ 0 := by norm_num
  apply (mul_right_inj' hc).mp
  ring_nf
  simpa [add_comm, sub_eq_iff_eq_add] using h1

section Ramanujan_qExpansion

open scoped ArithmeticFunction.sigma

/--
Helper: D applied to exp(2πinz) gives n * exp(2πinz).
This follows from: d/dz[exp(2πinz)] = 2πin * exp(2πinz),
so D[exp(2πinz)] = (2πi)⁻¹ * 2πin * exp(2πinz) = n * exp(2πinz).
-/
lemma D_exp_eq_n_mul (n : ℕ) (z : ℍ) :
    D (fun w : ℍ => cexp (2 * π * I * n * w)) z = n * cexp (2 * π * I * n * z) := by
  unfold D
  -- The key: (f ∘ ofComplex) agrees with f on the upper half-plane
  -- So their derivatives agree at points in ℍ
  have hcomp : deriv ((fun w : ℍ => cexp (2 * π * I * n * w)) ∘ ofComplex) z =
      deriv (fun w : ℂ => cexp (2 * π * I * n * w)) z := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw]
    rfl
  rw [hcomp]
  -- deriv of exp(c*z) is c*exp(c*z)
  have hderiv : deriv (fun w : ℂ => cexp (2 * π * I * n * w)) z =
      (2 * π * I * n) * cexp (2 * π * I * n * z) := by
    -- Use the derivative chain rule lemma directly
    have hdiff_lin : DifferentiableAt ℂ (fun w => 2 * π * I * n * w) (z : ℂ) := by fun_prop
    have hderiv_lin : deriv (fun w : ℂ => 2 * π * I * n * w) (z : ℂ) = 2 * π * I * n := by
      rw [deriv_const_mul _ differentiableAt_id]
      simp only [deriv_id'', mul_one]
    calc deriv (fun w : ℂ => cexp (2 * π * I * n * w)) z
        = cexp (2 * π * I * n * z) * deriv (fun w => 2 * π * I * n * w) z := by
            exact deriv_cexp hdiff_lin
      _ = cexp (2 * π * I * n * z) * (2 * π * I * n) := by rw [hderiv_lin]
      _ = (2 * π * I * n) * cexp (2 * π * I * n * z) := by ring
  rw [hderiv]
  -- Simplify (2πi)⁻¹ * (2πin) = n
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, ofReal_eq_zero,
      Real.pi_ne_zero, I_ne_zero, or_self]
  field_simp

/--
Key identity: The double sum ∑' (c,d), c * d^(k+1) * exp(2πi*z*cd) equals ∑' n, n * σ_k(n) * exp(2πi*n*z).
This follows from the definition σ_k(n) = ∑_{d|n} d^k and the identity n * σ_k(n) = ∑_{cd=n} c * d^(k+1).

The proof uses `tsum_sigma_eqn` and the fact that differentiation multiplies by the exponent factor.
-/
lemma tsum_sigma_deriv_eq {k : ℕ} (z : ℍ) :
    ∑' c : ℕ+ × ℕ+, (c.1 : ℂ) * (c.2 : ℂ) ^ (k + 1) * cexp (2 * π * I * z * c.1 * c.2) =
    ∑' n : ℕ+, (n : ℂ) * (σ k n : ℂ) * cexp (2 * π * I * n * z) := by
  -- The key identity: for each n, ∑_{cd=n} c * d^(k+1) = n * σ_k(n)
  -- Proof: ∑_{cd=n} c * d^(k+1) = ∑_{d|n} (n/d) * d^(k+1) = ∑_{d|n} n * d^k = n * σ_k(n)
  --
  -- Use sigmaAntidiagonalEquivProd to convert pairs (c,d) to divisor sums
  rw [← sigmaAntidiagonalEquivProd.tsum_eq]
  simp only [sigmaAntidiagonalEquivProd, mapdiv, PNat.mk_coe, Equiv.coe_fn_mk]
  -- Use summability to convert tsum over sigma to tsum over ℕ+
  have hsumm : Summable (fun c : (n : ℕ+) × {x // x ∈ (n : ℕ).divisorsAntidiagonal} ↦
      (↑(c.snd.val.1) : ℂ) * ↑(c.snd.val.2) ^ (k + 1) *
      cexp (2 * π * I * z * c.snd.val.1 * c.snd.val.2)) := by
    -- Summability follows from bounds adapting summable_auxil_1:
    -- For (a,b) ∈ divisorsAntidiagonal n: a * b = n, so
    --   a * b^(k+1) = n * b^k ≤ n^(k+1) (since b | n implies b ≤ n)
    --   |exp(2πi*z*ab)| = |exp(2πi*n*z)| (exponential decay)
    -- Sum over divisors: card(divisors) * n^(k+1) * |exp| ≤ n^(k+2) * |exp|
    -- Outer sum converges by hsum (k+2) z
    -- See summable_auxil_1 and mathlib's summable_divisorsAntidiagonal_aux for pattern
    sorry
  rw [hsumm.tsum_sigma]
  apply tsum_congr
  intro n
  rw [tsum_fintype, Finset.univ_eq_attach]
  -- For each n, show ∑_{(c,d) with cd=n} c * d^(k+1) = n * σ_k(n)
  have hdiv := @Nat.sum_divisorsAntidiagonal' ℂ _ (fun (x : ℕ) => fun (y : ℕ) =>
    (x : ℂ) * (y : ℂ) ^ (k + 1) * cexp (2 * π * I * z * x * y)) n
  simp only at hdiv
  have H := Finset.sum_attach ((n : ℕ).divisorsAntidiagonal) (fun (x : ℕ × ℕ) =>
    (x.1 : ℂ) * (x.2 : ℂ) ^ (k + 1) * cexp (2 * π * I * z * x.1 * x.2))
  simp only at H
  rw [H, hdiv]
  -- Now show: ∑_{i|n} ↑(n/i) * i^(k+1) * exp(2πi * z * ↑(n/i) * i) = n * σ_k(n) * exp(2πinz)
  -- Note: Nat.sum_divisorsAntidiagonal' produces ↑(↑n / i) which is ℕ division cast to ℂ
  --
  -- Key identity for i | n: ↑((n/i : ℕ) * i : ℕ) = ↑n via Nat.div_mul_cancel
  -- This gives: ↑(n/i) * ↑i = ↑n (using ← Nat.cast_mul)
  -- Then: ↑(n/i) * i^(k+1) = ↑(n/i) * i * i^k = n * i^k
  -- And: exp(2πi*z*↑(n/i)*i) = exp(2πi*n*z) since ↑(n/i)*i = n
  --
  -- Convert each term using ← Nat.cast_mul and Nat.div_mul_cancel
  have hterm_eq : ∀ i ∈ (n : ℕ).divisors,
      (((n : ℕ) / i : ℕ) : ℂ) * (i : ℂ) ^ (k + 1) *
        cexp (2 * π * I * z * (((n : ℕ) / i : ℕ) : ℂ) * (i : ℂ)) =
      (n : ℂ) * (i : ℂ) ^ k * cexp (2 * π * I * n * z) := by
    intro i hi
    have hdvd : i ∣ (n : ℕ) := Nat.dvd_of_mem_divisors hi
    -- Key: ↑((n/i) * i : ℕ) = ↑n, so ↑(n/i) * ↑i = ↑n
    have hprod : (((n : ℕ) / i : ℕ) : ℂ) * (i : ℂ) = (n : ℂ) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
    -- Coefficient: ↑(n/i) * i^(k+1) = ↑(n/i) * i * i^k = n * i^k
    have hcoeff : (((n : ℕ) / i : ℕ) : ℂ) * (i : ℂ) ^ (k + 1) = (n : ℂ) * (i : ℂ) ^ k := by
      calc (((n : ℕ) / i : ℕ) : ℂ) * (i : ℂ) ^ (k + 1)
          = (((n : ℕ) / i : ℕ) : ℂ) * (i : ℂ) * (i : ℂ) ^ k := by ring
        _ = (n : ℂ) * (i : ℂ) ^ k := by rw [hprod]
    -- Exponential: ↑(n/i) * i = n, so exp(...) = exp(2πi*n*z)
    -- Note: ((n : ℕ) / i) is ℕ division, which gets coerced to ℂ in this context
    have hexp : cexp (2 * π * I * z * (((n : ℕ) / i : ℕ) : ℂ) * (i : ℂ)) =
        cexp (2 * π * I * n * z) := by
      congr 1
      -- Rearrange to use hprod: ↑(↑n/i) * ↑i = ↑↑n (without using push_cast)
      have hrearr : (2 : ℂ) * π * I * z * (((n : ℕ) / i : ℕ) : ℂ) * (i : ℂ) =
          2 * π * I * z * ((((n : ℕ) / i : ℕ) : ℂ) * (i : ℂ)) := by ring
      rw [hrearr, hprod]
      ring
    rw [hcoeff, hexp]
  -- Apply the term rewrite to the sum using direct rewrites
  rw [Finset.sum_congr rfl hterm_eq, ← Finset.sum_mul, ← Finset.mul_sum]
  -- Now show: ∑ i ∈ n.divisors, (i : ℂ)^k = (σ k n : ℂ) using sigma_apply
  have hsigma_cast : ∑ i ∈ ((n : ℕ)).divisors, ((i : ℂ)) ^ k = ((σ k n) : ℂ) := by
    rw [ArithmeticFunction.sigma_apply]
    simp only [Nat.cast_sum, Nat.cast_pow]
  rw [hsigma_cast]

/--
The normalized derivative D multiplies q-expansion coefficients by n.
Since E₄ = 1 + 240·Σσ₃(n)·qⁿ, we have D(E₄) = 240·Σn·σ₃(n)·qⁿ.
-/
lemma D_E4_qexp (z : ℍ) :
    D E₄.toFun z = 240 * ∑' (n : ℕ+), n * (σ 3 n) * cexp (2 * π * Complex.I * n * z) := by
  -- Step 1: Express E₄ using q-expansion
  -- E₄(z) = 1 + 240 * ∑' n : ℕ+, σ₃(n) * exp(2πi·z·n) from E_k_q_expansion
  have hE4 : ∀ w : ℍ, E₄.toFun w = 1 + 240 * ∑' (n : ℕ+), (σ 3 n) * cexp (2 * π * I * w * n) := by
    intro w
    -- E₄.toFun = E₄ by coercion, and E₄ = E 4 by definition
    have hE : E₄.toFun w = E 4 (by norm_num) w := by rfl
    have hqexp := E_k_q_expansion 4 (by norm_num) (by exact Nat.even_iff.mpr rfl) w
    -- hqexp uses ↑4 while target uses 4; they are equal
    simp only [Nat.cast_ofNat, Nat.succ_sub_succ_eq_sub, tsub_zero] at hqexp
    rw [hE, hqexp]
    -- Now goal is: 1 + (1/riemannZeta 4) * ((-2πi)^4 / 3!) * ∑'... = 1 + 240 * ...
    -- Need to show coefficient = 240
    -- Using riemannZeta_four : riemannZeta 4 = π^4 / 90
    congr 1
    have hzeta : riemannZeta 4 = (π : ℂ) ^ 4 / 90 := by
      simp only [riemannZeta_four]
    -- Coefficient = (1/(π^4/90)) * ((-2πi)^4 / 6) = (90/π^4) * (16π^4) / 6 = 240
    have hcoeff : (1 / riemannZeta 4) * ((-2 * π * I) ^ 4 / Nat.factorial 3) = (240 : ℂ) := by
      rw [hzeta]
      -- (-2πi)^4 = 16π^4 since I^4 = 1
      have hI4 : I ^ 4 = (1 : ℂ) := by norm_num [pow_succ, I_sq]
      have h1 : (-2 * (π : ℂ) * I) ^ 4 = 16 * (π : ℂ) ^ 4 := by
        have : (-2 * (π : ℂ) * I) ^ 4 = (-2) ^ 4 * (π : ℂ) ^ 4 * I ^ 4 := by ring
        rw [this, hI4]
        norm_num
      rw [h1]
      simp only [Nat.factorial_succ, Nat.reduceAdd]
      have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      field_simp
      ring
    convert mul_comm _ _ using 1
    rw [hcoeff]
    ring
  -- Step 2: Compute D of the q-expansion using deriv-tsum interchange
  -- We use D_exp_eq_n_mul for individual terms and the tsum-deriv interchange
  unfold D
  -- Express the derivative in terms of the q-expansion
  have hz' : 0 < (z : ℂ).im := z.im_pos
  -- The composition E₄.toFun ∘ ofComplex agrees with the q-expansion on ℍ'
  have hE4' : ∀ w : ℂ, 0 < w.im →
      (E₄.toFun ∘ ofComplex) w = 1 + 240 * ∑' (n : ℕ+), (σ 3 n) * cexp (2 * π * I * w * n) := by
    intro w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw]
    exact hE4 ⟨w, hw⟩
  -- deriv of constant + scalar * tsum = 0 + scalar * deriv(tsum)
  -- For the tsum, each term's derivative is: σ₃(n) * (2πin) * exp(2πinw)
  -- Using hasDerivAt_tsum_fun or derivWithin_tsum_fun' from tsumderivWithin.lean
  --
  -- **Full Proof Strategy** (detailed steps):
  --
  -- 1. Convert deriv to derivWithin on ℍ' (open set)
  -- 2. Use derivWithin_tsum_fun' to interchange deriv with tsum:
  --    derivWithin (∑' f_n) ℍ' z = ∑' derivWithin f_n ℍ' z
  -- 3. For each term: derivWithin (σ₃(n) * exp(2πinw)) ℍ' w = σ₃(n) * 2πin * exp(2πinw)
  -- 4. Simplify: (2πi)⁻¹ * σ₃(n) * 2πin * exp(2πinz) = n * σ₃(n) * exp(2πinz)
  --
  -- Requirements for derivWithin_tsum_fun':
  -- (a) ℍ' is open ✓ (upper_half_plane_isOpen)
  -- (b) Summability: ∀ w ∈ ℍ', Summable (n ↦ σ₃(n) * exp(2πinw))
  --     This follows from exponential decay (summable_auxil_1 with k=0)
  -- (c) Uniform derivative bound: ∃ u summable, ‖derivWithin (f n)‖ ≤ u n on compact K ⊆ ℍ'
  --     Since σ₃(n) ≤ n⁴ and derivatives add a factor of 2πn, we get n⁵ * |q|^n
  --     This is bounded by iter_deriv_comp_bound3
  -- (d) Each term differentiable: z ↦ σ₃(n) * exp(2πinz) is holomorphic
  --
  -- The infrastructure from summable_lems.lean handles most of this.
  -- Key lemmas: summable_auxil_1, iter_deriv_comp_bound2/3
  sorry

/--
The q-expansion identity E₂E₄ - E₆ = 720·Σn·σ₃(n)·qⁿ.
This follows from Ramanujan's formula: E₂E₄ - E₆ = 3·D(E₄),
combined with D(E₄) = 240·Σn·σ₃(n)·qⁿ (since D multiplies q-coefficients by n).
-/
theorem E₂_mul_E₄_sub_E₆ (z : ℍ) :
    (E₂ z) * (E₄ z) - (E₆ z) = 720 * ∑' (n : ℕ+), n * (σ 3 n) * cexp (2 * π * Complex.I * n * z)
    := by
  -- From ramanujan_E₄: D E₄ = (1/3) * (E₂ * E₄ - E₆)
  -- So: E₂ * E₄ - E₆ = 3 * D E₄
  have hRam : (E₂ z) * (E₄ z) - (E₆ z) = 3 * D E₄.toFun z := by
    -- ramanujan_E₄ : D E₄.toFun = 3⁻¹ * (E₂ * E₄.toFun - E₆.toFun)
    -- Evaluating at z and rearranging gives the result
    have h3 : (3 : ℂ) ≠ 0 := by norm_num
    have h := congrFun ramanujan_E₄ z
    -- h : D E₄.toFun z = (3⁻¹ * (E₂ * E₄.toFun - E₆.toFun)) z
    -- Instead of simp, unfold Pi.mul directly
    -- (c * f) z where c : ℂ and f : ℍ → ℂ evaluates to c * f z
    -- But the * here might be Pi.mul with c as constant function
    -- Let's work around by computing the value directly
    calc E₂ z * E₄ z - E₆ z
        = E₂ z * E₄.toFun z - E₆.toFun z := by rfl
      _ = 3 * (3⁻¹ * (E₂ z * E₄.toFun z - E₆.toFun z)) := by field_simp
      _ = 3 * D E₄.toFun z := by
          congr 1
          -- The RHS of h is (3⁻¹ * (E₂ * E₄.toFun - E₆.toFun)) z
          -- We need to show this equals 3⁻¹ * (E₂ z * E₄.toFun z - E₆.toFun z)
          -- This follows from how Pi multiplication works
          simp only [Pi.mul_apply, Pi.sub_apply] at h
          exact h.symm
  -- Substitute D(E₄) = 240 * ∑' n, n * σ₃(n) * q^n
  rw [hRam, D_E4_qexp]
  ring

end Ramanujan_qExpansion

/--
Prove modular linear differential equation satisfied by $F$.
-/
noncomputable def X₄₂ := 288⁻¹ * (E₄.toFun - E₂ * E₂)

noncomputable def Δ_fun := 1728⁻¹ * (E₄.toFun ^ 3 - E₆.toFun ^ 2)

noncomputable def F := (E₂ * E₄.toFun - E₆.toFun) ^ 2

theorem F_aux : D F = 5 * 6⁻¹ * E₂ ^ 3 * E₄.toFun ^ 2 - 5 * 2⁻¹ * E₂ ^ 2 * E₄.toFun * E₆.toFun
    + 5 * 6⁻¹ * E₂ * E₄.toFun ^ 3 + 5 * 3⁻¹ * E₂ * E₆.toFun ^ 2 - 5 * 6⁻¹ * E₄.toFun^2 * E₆.toFun
    := by
  rw [F, D_sq, D_sub, D_mul]
  · ring_nf
    rw [ramanujan_E₂, ramanujan_E₄, ramanujan_E₆]
    ext z
    simp
    ring_nf
  -- Holomorphicity of the terms
  · exact E₂_holo'
  · exact E₄.holo'
  · exact MDifferentiable.mul E₂_holo' E₄.holo'
  · exact E₆.holo'
  have h24 := MDifferentiable.mul E₂_holo' E₄.holo'
  exact MDifferentiable.sub h24 E₆.holo'


/--
Modular linear differential equation satisfied by `F`.
TODO: Move this to a more appropriate place.
-/
theorem MLDE_F : serre_D 12 (serre_D 10 F) = 5 * 6⁻¹ * F + 172800 * Δ_fun * X₄₂ := by
  ext x
  rw [X₄₂, Δ_fun, serre_D, serre_D, F_aux]
  unfold serre_D
  rw [F_aux]
  sorry

example : D (E₄.toFun * E₄.toFun) = 2 * 3⁻¹ * E₄.toFun * (E₂ * E₄.toFun - E₆.toFun) :=
  by
  rw [D_mul E₄.toFun E₄.toFun]
  · simp only [ramanujan_E₄]
    ring_nf
  · exact E₄.holo'
  · exact E₄.holo'

/-
Interaction between (Serre) derivative and restriction to the imaginary axis.
-/

/--
Chain rule for restriction to imaginary axis: `d/dt F(it) = -2π * (D F)(it)`.

This connects the real derivative along the imaginary axis to the normalized derivative D.
The key computation is:
- The imaginary axis is parametrized by g(t) = I * t
- By chain rule: d/dt F(it) = (dF/dz)(it) · (d/dt)(it) = F'(it) · I
- Since D = (2πi)⁻¹ · d/dz, we have F' = 2πi · D F
- So d/dt F(it) = 2πi · D F(it) · I = -2π · D F(it)
-/
theorem deriv_resToImagAxis_eq (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    {t : ℝ} (ht : 0 < t) :
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
  ring_nf; simp only [I_sq]; ring

/--
If $F$ is a modular form where $F(it)$ is positive for sufficiently large $t$ (i.e. constant term
is positive) and the derivative is positive, then $F$ is also positive.

NOTE: A cleaner proof (without MDifferentiable hypothesis) is available in PR #213.
This PR should wait for #213 to merge first.
-/
theorem antiDerPos {F : ℍ → ℂ} {k : ℤ} (hF : ResToImagAxis.EventuallyPos F)
    (hDF : ResToImagAxis.Pos (D F)) : ResToImagAxis.Pos F := by
  -- See PR #213 (gauss-math-inc) for proof using StrictAntiOn.eventuallyPos_Ioi
  sorry

/--
Let $F : \mathbb{H} \to \mathbb{C}$ be a holomorphic function where $F(it)$ is real for all $t > 0$.
Assume that Serre derivative $\partial_k F$ is positive on the imaginary axis.
If $F(it)$ is positive for sufficiently large $t$, then $F(it)$ is positive for all $t > 0$.

Note: This is more subtle than `antiDerPos` because `serre_D k F = D F - (k/12) * E₂ * F`.
The proof requires analyzing the sign of `E₂` on the imaginary axis or using properties of
the specific functions involved.
-/
theorem antiSerreDerPos {F : ℍ → ℂ} {k : ℤ} (hFdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hSDF : ResToImagAxis.Pos (serre_D k F)) (hF : ResToImagAxis.EventuallyPos F) :
    ResToImagAxis.Pos F := by
  -- Strategy: "no last zero" argument.
  -- At a zero of F, serre_D k F = D F (since E₂ * F = E₂ * 0 = 0).
  -- So if serre_D k F > 0, then D F > 0 at that point.
  -- By deriv_resToImagAxis_eq, d/dt F(it) = -2π * D F(it), so derivative is negative.
  -- This means F is strictly decreasing at the zero, contradicting having a "last zero".
  refine ⟨hF.1, fun t ht => ?_⟩
  -- Define g(t) = (F.resToImagAxis t).re
  set g : ℝ → ℝ := fun s => (F.resToImagAxis s).re with hg_def
  -- We need to show g t > 0. By contradiction, suppose g t ≤ 0 for some t > 0.
  by_contra h_not_pos
  push_neg at h_not_pos
  -- Get eventual positivity: ∃ t₀, ∀ s ≥ t₀, g s > 0
  obtain ⟨t₀, ht₀_pos, heventual⟩ := hF.2
  -- g is continuous on (0, ∞)
  have hg_cont : ContinuousOn g (Set.Ioi 0) := by
    intro s hs
    have hdiff := ResToImagAxis.Differentiable F hFdiff s hs
    exact Complex.continuous_re.continuousAt.comp_continuousWithinAt
      hdiff.continuousAt.continuousWithinAt
  -- Case analysis: if t ≥ t₀, then g t > 0 by eventual positivity - contradiction
  by_cases ht_le_t₀ : t₀ ≤ t
  · -- t ≥ t₀, so by eventual positivity g t > 0, contradiction
    exact absurd (heventual t ht_le_t₀) (not_lt.mpr h_not_pos)
  · push_neg at ht_le_t₀
    -- Now t < t₀ and g t ≤ 0 but g t₀ > 0
    -- There is a "last zero" t* = sSup {s ∈ [t, t₀] | g s ≤ 0}
    set Z := {s ∈ Set.Icc t t₀ | g s ≤ 0} with hZ_def
    have ht_in_Z : t ∈ Z := by
      simp only [Z, Set.mem_setOf_eq, Set.mem_Icc, le_refl, ht_le_t₀.le, and_self, true_and]
      rw [hg_def]
      exact h_not_pos
    have hZ_nonempty : Z.Nonempty := ⟨t, ht_in_Z⟩
    have hZ_bddAbove : BddAbove Z := ⟨t₀, fun s hs => hs.1.2⟩
    set t_star := sSup Z with ht_star_def
    have ht_star_mem : t_star ∈ Set.Icc t t₀ := by
      refine ⟨le_csSup_of_le hZ_bddAbove ht_in_Z (le_refl t), ?_⟩
      exact csSup_le hZ_nonempty (fun s hs => hs.1.2)
    have ht_star_pos : 0 < t_star := lt_of_lt_of_le ht ht_star_mem.1
    -- g(t_star) ≤ 0 because Z is closed (g is continuous) and t_star = sSup Z
    have hg_cont_Icc : ContinuousOn g (Set.Icc t t₀) :=
      hg_cont.mono (fun x hx => lt_of_lt_of_le ht hx.1)
    have hZ_closed : IsClosed Z := by
      have hZ_eq : Z = Set.Icc t t₀ ∩ g ⁻¹' Set.Iic 0 := by ext x; simp [Z]
      rw [hZ_eq]
      exact hg_cont_Icc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hg_t_star_le : g t_star ≤ 0 :=
      (hZ_closed.csSup_mem hZ_nonempty ⟨t₀, fun s hs => hs.1.2⟩).2
    -- Also t_star < t₀ (otherwise g t₀ ≤ 0, contradicting eventual positivity)
    have ht_star_lt_t₀ : t_star < t₀ := by
      by_contra h_ge
      push_neg at h_ge
      have hg_t₀_pos := heventual t₀ (le_refl t₀)
      have hg_t₀_eq := ht_star_mem.2.antisymm h_ge ▸ hg_t_star_le
      linarith
    -- Actually g(t_star) = 0 (if g(t_star) < 0, there would be points past t_star with g ≤ 0)
    have hg_t_star_eq : g t_star = 0 := by
      by_contra h_ne
      have h_neg : g t_star < 0 := lt_of_le_of_ne hg_t_star_le h_ne
      -- g is continuous at t_star, so g < 0 in a neighborhood
      have hg_cont_at : ContinuousAt g t_star := (hg_cont t_star ht_star_pos).continuousAt
        (Ioi_mem_nhds ht_star_pos)
      obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp hg_cont_at (|g t_star| / 2)
        (by positivity)
      -- Choose s in (t_star, min(t_star + δ, t₀))
      have hδ'' : 0 < t₀ - t_star := by linarith
      set s := t_star + min δ (t₀ - t_star) / 2 with hs_def
      have hmin_pos : 0 < min δ (t₀ - t_star) := lt_min hδ_pos hδ''
      have hs_gt : t_star < s := by linarith [half_pos hmin_pos]
      have hs_dist : dist s t_star < δ := by
        simp only [Real.dist_eq, abs_of_pos (sub_pos.mpr hs_gt)]
        calc s - t_star = min δ (t₀ - t_star) / 2 := by linarith
          _ < min δ (t₀ - t_star) := half_lt_self hmin_pos
          _ ≤ δ := min_le_left _ _
      have hg_s_bound := hδ hs_dist
      simp only [Real.dist_eq, abs_lt] at hg_s_bound
      have hg_s_neg : g s < 0 := by
        have habs : |g t_star| = -g t_star := abs_of_neg h_neg
        linarith [hg_s_bound.2]
      -- So s ∈ Z but s > t_star, contradicting t_star = sSup Z
      have hs_in_Z : s ∈ Z := by
        simp only [Z, Set.mem_setOf_eq, Set.mem_Icc]
        refine ⟨⟨le_of_lt (lt_of_le_of_lt ht_star_mem.1 hs_gt), ?_⟩, le_of_lt hg_s_neg⟩
        have h1 : s = t_star + min δ (t₀ - t_star) / 2 := by linarith
        have h2 : s ≤ t_star + (t₀ - t_star) / 2 := by linarith [min_le_right δ (t₀ - t_star)]
        linarith
      have : s ≤ t_star := le_csSup hZ_bddAbove hs_in_Z
      linarith
    -- Now we have g(t_star) = 0, i.e., F.resToImagAxis t_star = 0 (using that F is real)
    have hF_t_star_eq : F.resToImagAxis t_star = 0 := by
      have hreal := hF.1 t_star ht_star_pos
      simp only [Complex.ext_iff, Complex.zero_re, Complex.zero_im]
      exact ⟨hg_t_star_eq, hreal⟩
    -- At t_star, serre_D k F = D F (since F = 0 there)
    have hserre_eq_D : (serre_D k F).resToImagAxis t_star = (D F).resToImagAxis t_star := by
      unfold serre_D
      simp only [Pi.sub_apply, Pi.mul_apply,
        Function.resToImagAxis_apply, ResToImagAxis, ht_star_pos, ↓reduceDIte]
      have hF_zero : F ⟨I * t_star, by simp [ht_star_pos]⟩ = 0 := by
        have := hF_t_star_eq
        simp only [Function.resToImagAxis_apply, ResToImagAxis, ht_star_pos, ↓reduceDIte] at this
        exact this
      rw [hF_zero, mul_zero, sub_zero]
    -- serre_D k F is positive at t_star
    have hSDF_pos : 0 < ((serre_D k F).resToImagAxis t_star).re := hSDF.2 t_star ht_star_pos
    -- So D F is positive at t_star
    have hDF_pos : 0 < ((D F).resToImagAxis t_star).re := by rw [← hserre_eq_D]; exact hSDF_pos
    -- By deriv_resToImagAxis_eq: deriv F.resToImagAxis t_star = -2π * (D F).resToImagAxis t_star
    have hF_deriv : deriv F.resToImagAxis t_star = -2 * π * (D F).resToImagAxis t_star :=
      deriv_resToImagAxis_eq F hFdiff ht_star_pos
    -- deriv g t_star = (deriv F.resToImagAxis t_star).re < 0
    have hFdiff_at := ResToImagAxis.Differentiable F hFdiff t_star ht_star_pos
    have hDF_real := hSDF.1 t_star ht_star_pos
    rw [hserre_eq_D] at hDF_real
    have hg_deriv_neg : deriv g t_star < 0 := by
      -- deriv g = deriv (Complex.re ∘ F.resToImagAxis) = re (deriv F.resToImagAxis)
      -- Use HasFDerivAt.comp_hasDerivAt with the chain rule
      have hF_hasDerivAt : HasDerivAt F.resToImagAxis (deriv F.resToImagAxis t_star) t_star :=
        hFdiff_at.hasDerivAt
      have hg_hasDerivAt : HasDerivAt g (deriv F.resToImagAxis t_star).re t_star := by
        simp only [hg_def]
        exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t_star hF_hasDerivAt
      have hg_deriv_eq : deriv g t_star = (deriv F.resToImagAxis t_star).re := hg_hasDerivAt.deriv
      rw [hg_deriv_eq, hF_deriv]
      -- (-2 * π * (D F).resToImagAxis t_star).re < 0
      -- Since (D F).resToImagAxis t_star is real (im = 0), and -2π is real, this simplifies
      have h2pi : (0 : ℝ) < 2 * π := by positivity
      -- Write -2 * π as ofReal (-2 * π) to use re_ofReal_mul
      have hre_eq : (-2 * ↑π * (D F).resToImagAxis t_star).re =
          -2 * π * ((D F).resToImagAxis t_star).re := by
        rw [show (-2 : ℂ) * ↑π = ↑((-2 : ℝ) * π) by simp [Complex.ofReal_mul]]
        rw [Complex.re_ofReal_mul]
      rw [hre_eq]
      linarith [mul_pos h2pi hDF_pos]
    -- g(t_star) = 0 and g'(t_star) < 0 means g becomes negative just past t_star
    -- But for s > t_star (and s < t₀), we must have g s > 0 (since t_star = sSup Z)
    have hg_pos_after : ∀ s ∈ Set.Ioo t_star t₀, 0 < g s := by
      intro s ⟨hs_gt, hs_lt⟩
      by_contra h_not_pos_s
      push_neg at h_not_pos_s
      have hs_in_Z : s ∈ Z := by
        simp only [Z, Set.mem_setOf_eq, Set.mem_Icc]
        refine ⟨⟨le_of_lt (lt_of_le_of_lt ht_star_mem.1 hs_gt), le_of_lt hs_lt⟩, h_not_pos_s⟩
      have : s ≤ t_star := le_csSup hZ_bddAbove hs_in_Z
      linarith
    -- g is differentiable at t_star
    have hg_diff : DifferentiableAt ℝ g t_star := by
      simp only [hg_def]
      exact Complex.reCLM.differentiable.differentiableAt.comp t_star hFdiff_at
    -- By definition of derivative: f'(a) < 0 means f(a + ε) < f(a) for small ε > 0
    have h_decrease : ∃ ε > 0, ε < t₀ - t_star ∧ g (t_star + ε) < g t_star := by
      have hδ' : 0 < t₀ - t_star := by linarith
      -- Use eventually_nhdsWithin_sign_eq_of_deriv_neg: if deriv g x₀ < 0 and g x₀ = 0,
      -- then locally sign(g x) = sign(x₀ - x)
      have hsign := eventually_nhdsWithin_sign_eq_of_deriv_neg hg_deriv_neg hg_t_star_eq
      -- hsign : ∀ᶠ x in nhds t_star, SignType.sign (g x) = SignType.sign (t_star - x)
      -- Get an ε-ball where this holds
      rw [Filter.Eventually, Metric.mem_nhds_iff] at hsign
      obtain ⟨δ, hδ_pos, hδ_ball⟩ := hsign
      -- Choose ε = min(δ/2, (t₀ - t_star)/2)
      set ε := min (δ / 2) ((t₀ - t_star) / 2) with hε_def
      have hε_pos : 0 < ε := lt_min (by linarith) (by linarith)
      refine ⟨ε, hε_pos, ?_, ?_⟩
      · -- ε < t₀ - t_star
        calc ε ≤ (t₀ - t_star) / 2 := min_le_right _ _
          _ < t₀ - t_star := by linarith
      · -- g (t_star + ε) < g t_star
        have hε_in_ball : t_star + ε ∈ Metric.ball t_star δ := by
          simp only [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos hε_pos]
          calc ε ≤ δ / 2 := min_le_left _ _
            _ < δ := by linarith
        have hsign_at := hδ_ball hε_in_ball
        -- hsign_at : t_star + ε ∈ {x | SignType.sign (g x) = SignType.sign (t_star - x)}
        simp only [Set.mem_setOf_eq] at hsign_at
        -- hsign_at : SignType.sign (g (t_star + ε)) = SignType.sign (t_star - (t_star + ε))
        have hneg_ε : t_star - (t_star + ε) = -ε := by ring
        have hneg_ε_lt : -ε < 0 := neg_neg_of_pos hε_pos
        rw [hneg_ε, sign_neg hneg_ε_lt] at hsign_at
        -- sign (g (t_star + ε)) = -1 (i.e., SignType.neg) means g (t_star + ε) < 0
        have hg_neg : g (t_star + ε) < 0 := sign_eq_neg_one_iff.mp hsign_at
        rw [hg_t_star_eq]
        exact hg_neg
    obtain ⟨ε, hε_pos, hε_small, hg_decrease⟩ := h_decrease
    have hs_in_Ioo : t_star + ε ∈ Set.Ioo t_star t₀ := by
      constructor
      · linarith
      · linarith
    have hg_s_pos : 0 < g (t_star + ε) := hg_pos_after (t_star + ε) hs_in_Ioo
    rw [hg_t_star_eq] at hg_decrease
    linarith
