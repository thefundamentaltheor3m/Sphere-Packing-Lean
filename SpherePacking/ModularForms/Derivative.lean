import SpherePacking.ModularForms.Eisenstein

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
    _ = (2 * π * I)⁻¹ * deriv (F ∘ ofComplex) z + (2 * π * I)⁻¹ * deriv (G ∘ ofComplex) z := by
        rw [mul_add]
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
    _ = (2 * π * I)⁻¹ * deriv (F ∘ ofComplex) z - (2 * π * I)⁻¹ * deriv (G ∘ ofComplex) z
      := by rw [mul_sub]
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
    : D (F * G) = D F * G + F * D G := by
  ext z
  have h : deriv ((F ∘ ofComplex) * (G ∘ ofComplex)) z =
      deriv (F ∘ ofComplex) z * G z + F z * deriv (G ∘ ofComplex) z := by
    have hFz := MDifferentiableAt_DifferentiableAt (hF z)
    have hGz := MDifferentiableAt_DifferentiableAt (hG z)
    rw [deriv_mul hFz hGz]
    simp only [Function.comp_apply, ofComplex_apply]
  calc
    D (F * G) z
    _ = (2 * π * I)⁻¹ * deriv (F ∘ ofComplex * G ∘ ofComplex) z := by rfl
    _ = (2 * π * I)⁻¹ * (deriv (F ∘ ofComplex) z * G z + F z * deriv (G ∘ ofComplex) z)
      := by rw [h]
    _ = (2 * π * I)⁻¹ * deriv (F ∘ ofComplex) z * G z
        + F z * ((2 * π * I)⁻¹ * deriv (G ∘ ofComplex) z) := by ring_nf
    _ = D F z * G z + F z * D G z := by rfl

@[simp]
theorem D_sq (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    D (F ^ 2) = 2 * F * D F := by
  calc
    D (F ^ 2) = D F * F + F * D F := by rw [pow_two, D_mul F F hF hF]
    _ = 2 * F * D F := by ring_nf

@[simp]
theorem D_cube (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    D (F ^ 3) = 3 * F ^ 2 * D F := by
  have hF2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F ^ 2) := by rw [pow_two]; exact MDifferentiable.mul hF hF
  calc
    D (F ^ 3) = D (F * F ^ 2) := by ring_nf
    _ = D F * F ^ 2 + F * D (F ^ 2) := by rw [D_mul F (F ^ 2) hF hF2]
    _ = D F * F ^ 2 + F * (2 * F * D F) := by rw [D_sq F hF]
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
theorem serre_D_add (k : ℂ) (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) : serre_D k (F + G) = serre_D k F + serre_D k G := by
  ext z
  simp only [serre_D, Pi.add_apply, D_add F G hF hG]
  ring_nf

theorem serre_D_sub (k : ℂ) (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) : serre_D k (F - G) = serre_D k F - serre_D k G := by
  ext z
  simp only [serre_D, Pi.sub_apply, D_sub F G hF hG]
  ring_nf

theorem serre_D_smul (k : ℂ) (c : ℂ) (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    serre_D k (c • F) = c • serre_D k F := by
  ext z
  rw [Pi.smul_apply, serre_D, serre_D, D_smul _ _ hF]
  simp
  ring_nf

theorem serre_D_mul (k₁ k₂ : ℂ) (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) :
    serre_D (k₁ + k₂) (F * G) = (serre_D k₁ F) * G + F * serre_D k₂ G := by
  ext z
  rw [serre_D, D_mul _ _ hF hG]
  simp [Pi.add_apply, Pi.mul_apply] at *
  rw [serre_D, serre_D]
  ring_nf

/--
The Serre derivative preserves MDifferentiability.
If `F : ℍ → ℂ` is MDifferentiable, then `serre_D k F` is also MDifferentiable.
-/
theorem serre_D_differentiable {F : ℍ → ℂ} {k : ℂ}
    (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (serre_D k F) := by
  have h_term : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => k * 12⁻¹ * E₂ z * F z) := by
    have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => (k * 12⁻¹) * (E₂ z * F z)) :=
      MDifferentiable.mul mdifferentiable_const (E₂_holo'.mul hF)
    convert h1 using 1; ext z; simp only [mul_assoc]
  exact (D_differentiable hF).sub h_term

/-! ### Helper lemmas for D_slash

These micro-lemmas compute derivatives of the components in the slash action formula.
-/

section DSlashHelpers

open ModularGroup

variable (γ : SL(2, ℤ))

/-- Derivative of the denominator function: d/dz[cz + d] = c. -/
lemma deriv_denom (z : ℂ) :
    deriv (fun w => denom γ w) z = ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) := by
  simp only [denom]
  rw [deriv_add_const, deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one]; simp

/-- Derivative of the numerator function: d/dz[az + b] = a. -/
lemma deriv_num (z : ℂ) :
    deriv (fun w => num γ w) z = ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) := by
  simp only [num]
  rw [deriv_add_const, deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one]; simp

/-- Differentiability of denom. -/
lemma differentiableAt_denom (z : ℂ) :
    DifferentiableAt ℂ (fun w => denom γ w) z := by
  simp only [denom]
  fun_prop

/-- Differentiability of num. -/
lemma differentiableAt_num (z : ℂ) :
    DifferentiableAt ℂ (fun w => num γ w) z := by
  simp only [num]
  fun_prop

/-- Derivative of the Möbius transformation: d/dz[(az+b)/(cz+d)] = 1/(cz+d)².
Uses det(γ) = 1: a(cz+d) - c(az+b) = ad - bc = 1. -/
lemma deriv_moebius (z : ℂ) (hz : denom γ z ≠ 0) :
    deriv (fun w => num γ w / denom γ w) z = 1 / (denom γ z) ^ 2 := by
  have hdiff_num := differentiableAt_num γ z
  have hdiff_denom := differentiableAt_denom γ z
  have hderiv : HasDerivAt (fun w => num γ w / denom γ w)
      ((deriv (fun w => num γ w) z * denom γ z - num γ z * deriv (fun w => denom γ w) z)
        / (denom γ z) ^ 2) z := hdiff_num.hasDerivAt.div hdiff_denom.hasDerivAt hz
  rw [hderiv.deriv, deriv_num, deriv_denom]
  -- det(γ) = 1 in ℂ
  have hdet : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * (γ 1 1) -
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) * (γ 1 0) = 1 := by
    have hdet' := Matrix.SpecialLinearGroup.det_coe γ
    simp only [Matrix.det_fin_two, ← Int.cast_mul, ← Int.cast_sub] at hdet' ⊢
    exact mod_cast hdet'
  -- Normalize GL → Matrix ℤ coercions via simp
  simp only [num, denom] at *
  simp only [show (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) by simp,
    show (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) by simp,
    show (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) by simp,
    show (((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ) by simp]
  -- Numerator: a * denom - num * c = ad - bc = 1
  have hnum_eq : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) *
      (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * z + ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ)) -
      (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * z + ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ)) *
        ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) = 1 := by linear_combination hdet
  simp only [hnum_eq, one_div]

/-- Derivative of denom^(-k): d/dz[(cz+d)^(-k)] = -k * c * (cz+d)^(-k-1). -/
lemma deriv_denom_zpow (k : ℤ) (z : ℂ) (hz : denom γ z ≠ 0) :
    deriv (fun w => (denom γ w) ^ (-k)) z =
        (-k : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * (denom γ z) ^ (-k - 1) := by
  have hdiff := differentiableAt_denom γ z
  have hderiv_zpow := hasDerivAt_zpow (-k) (denom γ z) (Or.inl hz)
  have hderiv_denom : HasDerivAt (fun w => denom γ w)
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) z := by rw [← deriv_denom]; exact hdiff.hasDerivAt
  have hcomp := hderiv_zpow.comp z hderiv_denom
  have heq : (fun w => w ^ (-k)) ∘ (fun w => denom γ w) = (fun w => (denom γ w) ^ (-k)) := rfl
  rw [← heq, hcomp.deriv]; simp only [Int.cast_neg]; ring

end DSlashHelpers

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
  -- Computation (product rule + chain rule):
  -- D(F ∣[k] γ) = (2πi)⁻¹ * deriv[F(γ•·) * denom^(-k)]
  --   = (2πi)⁻¹ * [F(γ•z)*(-k*c*denom^(-k-1)) + deriv[F](γ•z)*(1/denom²)*denom^(-k)]
  --   = (D F ∣[k+2] γ) - k*(2πi)⁻¹*(c/denom)*(F ∣[k] γ)
  ext z
  unfold D
  simp only [Pi.sub_apply]
  -- Key facts about denom
  have hz_denom_ne : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  -- The derivative computation on ℂ using Filter.EventuallyEq.deriv_eq
  -- (F ∣[k] γ) ∘ ofComplex agrees with F(num/denom) * denom^(-k) on ℍ
  have hcomp : deriv (((F ∣[k] γ)) ∘ ofComplex) z =
      deriv (fun w => (F ∘ ofComplex) (num γ w / denom γ w) * (denom γ w) ^ (-k)) z := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw]
    rw [ModularForm.SL_slash_apply (f := F) (k := k) γ ⟨w, hw⟩]
    -- Key: (γ • ⟨w, hw⟩ : ℂ) = num γ w / denom γ w
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
  -- Final algebraic manipulation
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
Serre derivative is equivariant under the slash action. More precisely, if `F` is invariant
under the slash action of weight `k`, then `serre_D k F` is invariant under the slash action
of weight `k + 2`.
-/
theorem serre_D_slash_equivariant (k : ℤ) (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    ∀ γ : SL(2, ℤ), serre_D k F ∣[k + 2] γ = serre_D k (F ∣[k] γ) := by sorry

theorem serre_D_slash_invariant (k : ℤ) (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (γ : SL(2, ℤ)) (h : F ∣[k] γ = F) :
    serre_D k F ∣[k + 2] γ = serre_D k F := by
  rw [serre_D_slash_equivariant, h]
  exact hF

/--
Serre derivative of Eisenstein series. Use `serre_D_slash_invariant` and compare constant terms.
Note that the dimensions of the spaces of modular forms are all 1.
-/
theorem ramanujan_E₂' : serre_D 1 E₂ = - 12⁻¹ * E₄.toFun := by sorry

theorem ramanujan_E₄' : serre_D 4 E₄.toFun = - 3⁻¹ * E₆.toFun := by sorry

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
If $F$ is a modular form where $F(it)$ is positive for sufficiently large $t$ (i.e. constant term
is positive) and the derivative is positive, then $F$ is also positive.
-/
theorem antiDerPos {F : ℍ → ℂ} {k : ℤ} (hF : ResToImagAxis.EventuallyPos F)
    (hDF : ResToImagAxis.Pos (D F)) : ResToImagAxis.Pos F := by
  sorry

/--
Let $F : \mathbb{H} \to \mathbb{C}$ be a holomorphic function where $F(it)$ is real for all $t > 0$.
Assume that Serre derivative $\partial_k F$ is positive on the imaginary axis.
If $F(it)$ is positive for sufficiently large $t$, then $F(it)$ is positive for all $t > 0$.
-/
theorem antiSerreDerPos {F : ℍ → ℂ} {k : ℤ} (hSDF : ResToImagAxis.Pos (serre_D k F))
    (hF : ResToImagAxis.EventuallyPos F) : ResToImagAxis.Pos F := by
  sorry
