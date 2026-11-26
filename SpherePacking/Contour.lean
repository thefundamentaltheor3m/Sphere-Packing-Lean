module

public import Mathlib

@[expose] public noncomputable section

universe u

open unitInterval Set Complex Real MeasureTheory

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

@[simp]
theorem circleMap_zero_arg (p : ℂ) (R : ℝ) : circleMap p R 0 = p + R := by
  simp [circleMap]

@[simp]
theorem circleMap_one_arg (p : ℂ) (R : ℝ) : circleMap p R (2 * π) = p + R := by
  simp [circleMap]

def circlePath (p : ℂ) (R : ℝ) : Path (p + R) (p + R) where
  toFun x := circleMap p R (2 * π * x)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

--#check curveIntegral
def Path.IsPiecewiseC1' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : E}
    (γ : Path a b) : Prop :=
  ∃ (n : ℕ) (t : Fin (n + 1) → ℝ), Monotone t ∧ t 0 = 0 ∧ t (Fin.last n) = 1 ∧
    ∀ i : Fin n, ContDiffOn ℝ 1 γ.extend (Icc (t i.castSucc) (t i.succ))

def Path.IsPiecewise {X : Type*} [TopologicalSpace X] {a b : X}
    (γ : Path a b) (P : {a : X} → {b : X} → Path a b → Prop) : Prop :=
  ∃ (n : ℕ) (t : Fin (n + 1) → I), Monotone t ∧ t 0 = 0 ∧ t (Fin.last n) = 1 ∧
    ∀ i : Fin n, P (Path.subpath γ (t i.castSucc) (t i.succ))

def PathIntegrable (f : ℂ → ℂ) {a b : ℂ} (γ : Path a b) : Prop :=
  IntervalIntegrable (fun z ↦ f (γ.extend z) * (deriv γ.extend z)) volume 0 1

abbrev Path.IsPiecewiseC1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : E}
    (γ : Path a b) : Prop :=
  IsPiecewise γ fun p ↦ ContDiffOn ℝ 1 p.extend I

/-- The contour integral `∫_γ f(z) dz` of `f : ℂ → E` along a path `γ` in `ℂ`, defined as
`∫ t in 0..1, γ'(t) • f (γ t)`. -/
noncomputable abbrev contourIntegral {a b : ℂ} (f : ℂ → E) (γ : Path a b) : E :=
  ∫ t in 0..1, deriv γ.extend t • f (γ.extend t)

notation3 "∮ "(...)" in "γ", "r:60:(scoped f => contourIntegral f γ) => r

/-- The contour integral is the curve integral of the 1-form `ω z = (v ↦ v • f z)`. -/
theorem contourIntegral_def {a b : ℂ} (f : ℂ → E) (γ : Path a b) :
    ∮ z in γ, f z = ∫ᶜ z in γ, ContinuousLinearMap.toSpanSingleton ℂ (f z) := by
  simp [contourIntegral, curveIntegral_eq_intervalIntegral_deriv]

variable {a b c : ℂ} (f : ℂ → ℂ) (γ : Path a b) (τ : Path b c)

theorem goal0 : ∮ z in γ, f z = ∫ z in 0..1, f (γ.extend z) * (deriv γ.extend z) := by
  simp [contourIntegral, mul_comm]

#check circleIntegral

--{E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℂ → E)

lemma integral_deriv_mul (f g : ℝ → ℂ) (u v a : ℝ) :
    ∫ x in (u * a)..(v * a), g x * deriv f x =
      ∫ x in u..v, g (a * x) * deriv (fun y ↦ f (a * y)) x := by
  rw [← intervalIntegral.smul_integral_comp_mul_right (a := u) (b := v) (fun x ↦ g x * deriv f x) a,
    real_smul]
  rw [← intervalIntegral.integral_const_mul ↑a fun x ↦ g (x * a) * deriv f (x * a)]
  congr! 1
  ext x
  rw [deriv_comp_mul_left]
  simp
  ring_nf

lemma integral_deriv_mul' (f g : ℝ → ℂ) (a : ℝ) :
    ∫ x in 0..a, g x * deriv f x =
      ∫ x in 0..1, g (a * x) * deriv (fun y ↦ f (a * y)) x := by
  simp [← integral_deriv_mul]

lemma integral_deriv_mul_add (f g : ℝ → ℂ) (u v a d : ℝ) :
    ∫ x in (u * a + d)..(v * a + d), g x * deriv f x =
      ∫ x in u..v, g (a * x + d) * deriv (fun y ↦ f (a * y + d)) x := by
  rw [mul_comm u a, mul_comm v a,
    ← intervalIntegral.smul_integral_comp_mul_add (fun x ↦ g x * deriv f x) a d, real_smul,
    ← intervalIntegral.integral_const_mul]
  congr! 1
  ext x
  rw [deriv_comp_mul_left a (fun y ↦ f (y + d)) x, deriv_comp_add_const]
  simp
  ring

lemma integral_deriv_mul_sub (f g : ℝ → ℂ) (u v a d : ℝ) :
    ∫ x in (u * a - d)..(v * a - d), g x * deriv f x =
      ∫ x in u..v, g (a * x - d) * deriv (fun y ↦ f (a * y - d)) x := by
  simpa [sub_eq_add_neg] using integral_deriv_mul_add f g u v a (-d)

--hasDerivAt_circleMap
theorem circleIntegral_eq_contourIntegral (f : ℂ → ℂ) (R : ℝ) :
    circleIntegral f c R = ∮ z in circlePath c R, f z := by
  rw [circleIntegral, goal0]
  calc
    ∫ (θ : ℝ) in 0..2 * π, deriv (circleMap c R) θ • f (circleMap c R θ)
      = ∫ (θ : ℝ) in 0 * (2 * π)..(1 * (2 * π)), deriv (circleMap c R) θ • f (circleMap c R θ) := by
      simp
    _ =  _ := by
      rw [← intervalIntegral.smul_integral_comp_mul_right _ (2 * π)]
      simp
      trans (∫ (x : ℝ) in 0..1, (2 * ↑π) * (circleMap 0 R (x * (2 * π)) * «I» * f (circleMap c R (x * (2 * π)))))
      · symm
        apply intervalIntegral.integral_const_mul
      apply intervalIntegral.integral_congr_uIoo (fun x hx ↦ ?_)
      rw [← mul_comm (f (circleMap c R (x * (2 * π))))]
      rw [mul_comm (2 * (↑π : ℂ)), mul_assoc]
      congr 2
      · simp [circlePath]
        rw [Path.extend_apply (ht := by simp_all; grind)]
        simp
        grind
      · simp only [zero_le_one, uIoo_of_le, mem_Ioo] at hx
        trans deriv (fun y ↦ circleMap c R (2 * π * y)) x
        swap
        · refine Eq.symm (Filter.EventuallyEq.deriv_eq ?_)
          unfold Filter.EventuallyEq
          refine eventually_nhds_iff.mpr ?_
          refine ⟨Ioo 0 1, ?_, isOpen_Ioo, by simpa⟩
          simp only [mem_Ioo, and_imp]
          intro y yp yl
          unfold circlePath
          rw [Path.extend_apply (ht := by grind)]
          simp
        symm
        trans (deriv ((circleMap c R) ∘ (fun (y : ℝ) ↦ (2 * π) * y))) x
        · rfl
        rw [deriv.scomp x ?_ (by fun_prop)]
        · simp only [deriv_const_mul_id', deriv_circleMap, real_smul, ofReal_mul, ofReal_ofNat]
          grind
        apply Differentiable.differentiableAt
        apply differentiable_circleMap

--(γ.trans τ).extend (2⁻¹ * x) = γ.extend x

lemma Path.trans_extend_two_inv_mul_of_le {X : Type*} [TopologicalSpace X] {x y z : X}
    (γ : Path x y) (τ : Path y z) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    (γ.trans τ).extend (2⁻¹ * t) = γ.extend t := by
  rw [Path.extend_apply _ (by simp; grind)]
  simp [Path.trans]
  grind

lemma Path.trans_extend_two_inv_mul_of_ge_inv_two {X : Type*} [TopologicalSpace X] {x y z : X}
    (γ : Path x y) (τ : Path y z) {t : ℝ} (ht : 2⁻¹ ≤ t) (ht' : t ≤ 1) :
    (γ.trans τ).extend t = τ.extend (2 * t - 1) := by
  rw [Path.extend_apply _ (by simp; grind)]
  simp [Path.trans]
  grind

lemma Path.deriv_trans_of_zero_lt_of_lt_two_inv {x : ℝ} (hx : 0 < x) (hx' : x < 2⁻¹) :
    deriv (γ.trans τ).extend x = 2 * deriv (γ.extend) (2 * x) := by
  trans deriv (fun z ↦ γ.extend (2 * z)) x
  · refine Filter.EventuallyEq.deriv_eq ?_
    unfold Filter.EventuallyEq
    refine eventually_nhds_iff.mpr ?_
    refine ⟨Ioo 0 2⁻¹, ?_, isOpen_Ioo, by grind⟩
    simp only [mem_Ioo, and_imp]
    intro y hy hy'
    rw [Path.extend_apply _ (by simp; grind)]
    simp [Path.trans]
    grind
  · rw [deriv_comp_mul_left]
    simp

lemma Path.deriv_trans_of_two_inv_lt_of_lt_one {x : ℝ} (hx : 2⁻¹ < x) (hx' : x < 1) :
    deriv (γ.trans τ).extend x = 2 * deriv (τ.extend) (2 * x - 1) := by
  trans deriv (fun z ↦ τ.extend (2 * z - 1)) x
  · refine Filter.EventuallyEq.deriv_eq ?_
    unfold Filter.EventuallyEq
    refine eventually_nhds_iff.mpr ?_
    refine ⟨Ioo 2⁻¹ 1, ?_, isOpen_Ioo, by grind⟩
    simp only [mem_Ioo, and_imp]
    intro y hy hy'
    rw [Path.extend_apply _ (by simp; grind)]
    simp [Path.trans]
    grind
  · rw [deriv_comp_mul_left 2 (fun y ↦ τ.extend (y - 1)) x, deriv_comp_sub_const]
    simp

theorem contourIntegral_append (hγ : PathIntegrable f γ) (hτ : PathIntegrable f τ) :
    ∮ z in γ.trans τ, f z = (∮ z in γ, f z) + ∮ z in τ, f z := by
  rw [goal0, goal0, goal0, ← intervalIntegral.integral_add_adjacent_intervals (a := 0) (c := 1) (b := 2⁻¹)]
  · congr 1
    · rw [integral_deriv_mul']
      apply intervalIntegral.integral_congr_uIoo (fun x hx ↦ ?_)
      congr! 1
      · simp at hx
        rw [Path.trans_extend_two_inv_mul_of_le _ _ (by grind) (by grind)]
      · refine Eq.symm (Filter.EventuallyEq.deriv_eq ?_)
        unfold Filter.EventuallyEq
        refine eventually_nhds_iff.mpr ?_
        refine ⟨Ioo 0 1, ?_, isOpen_Ioo, ?_⟩
        · grind [Path.trans_extend_two_inv_mul_of_le]
        simp at hx ⊢
        grind
    · trans ∫ (z : ℝ) in 2⁻¹..1, f (τ.extend (2 * z - 1)) * (2 * deriv (⇑τ.extend) (2 * z - 1))
      · refine intervalIntegral.integral_congr_Ioo_of_le (by grind) fun x hx ↦ ?_
        simp at hx
        rw [Path.trans_extend_two_inv_mul_of_ge_inv_two (ht := by grind) (ht' := by grind)]
        congr 1
        rw [Path.deriv_trans_of_two_inv_lt_of_lt_one _ _ hx.1 hx.2]
      have := integral_deriv_mul_sub τ.extend (fun x ↦ f (τ.extend x)) 2⁻¹ 1 2 1
      rw [show (2⁻¹ : ℝ) * 2 - 1 = 0 by norm_num, show (1 : ℝ) * 2 - 1 = 1 by norm_num] at this
      rw [this]
      clear this
      congr! 2 with x
      rw [deriv_comp_mul_left 2 (fun y ↦ τ.extend (y - 1)) x, deriv_comp_sub_const]
      simp
  · unfold PathIntegrable at hγ
    let h := fun z ↦ f (γ.extend z) * deriv (⇑γ.extend) z
    suffices IntervalIntegrable (fun z ↦ h (2 * z)) volume (0 / 2) (1 / 2) by
      replace this : IntervalIntegrable ((2 : ℂ) • fun z ↦ h (2 * z)) volume (0 / 2) (1 / 2) := by
        exact IntervalIntegrable.smul this 2
      simp only [zero_div, one_div] at this
      apply IntervalIntegrable.congr_uIoo this
      intro z
      simp only [inv_nonneg, Nat.ofNat_nonneg, uIoo_of_le, mem_Ioo, Pi.smul_apply, smul_eq_mul,
        and_imp, h]
      intro zp zl
      rw [Path.deriv_trans_of_zero_lt_of_lt_two_inv _ _ zp zl]
      nth_rw 2 [Path.extend_apply _ (by simp; grind)]
      simp [Path.trans]
      grind
    apply IntervalIntegrable.comp_mul_left
    · unfold h
      exact hγ
    · simp
    · simp
  · unfold PathIntegrable at hτ
    let h := fun z ↦ f (τ.extend z) * deriv (⇑τ.extend) z
    suffices IntervalIntegrable (fun z ↦ h (2 * z - 1)) volume ((0 + 1) / 2) ((1 + 1) / 2) by
      replace this : IntervalIntegrable ((2 : ℂ) • fun z ↦ h (2 * z - 1)) volume
          ((0 + 1) / 2) ((1 + 1) / 2) := by
        exact IntervalIntegrable.smul this 2
      rw [show ((0 : ℝ) + 1) / 2 = 2⁻¹ by norm_num, show ((1 : ℝ) + 1) / 2 = 1 by norm_num] at this
      apply IntervalIntegrable.congr_uIoo this
      intro z hz
      rw [uIoo_of_le (by norm_num), mem_Ioo] at hz
      obtain ⟨zp, zl⟩ := hz
      simp only [Pi.smul_apply, smul_eq_mul, h]
      rw [Path.deriv_trans_of_two_inv_lt_of_lt_one _ _ zp zl,
        Path.trans_extend_two_inv_mul_of_ge_inv_two _ _ zp.le zl.le]
      ring
    apply IntervalIntegrable.comp_mul_left (f := fun x ↦ h (x - 1))
    apply IntervalIntegrable.comp_sub_right
    · unfold h
      exact hτ
    · simp

theorem Function.const_hasDerivAt {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (x : 𝕜) (c : F) :
    HasDerivAt (Function.const 𝕜 c) 0 x := by
  convert hasDerivAt_const x c
  simp

@[simp]
theorem contourIntegral_of_path_refl (a : ℂ) (f : ℂ → ℂ) : ∮ z in Path.refl a, f z = 0 := by
  rw [goal0]
  trans ∫ (z : ℝ) in 0..1, 0
  · congr with x
    simp only [Path.refl_extend, ContinuousMap.const_apply, ContinuousMap.coe_const, mul_eq_zero]
    right
    apply HasDerivAt.deriv
    exact Function.const_hasDerivAt x a
  · simp

--#check contDiffOn

--def IsNice (p : Path a b) : Prop :=
-- Set.piecewise

--Reparametrization
theorem contourIntegral_path_congr {a b : ℂ} (f : ℂ → ℂ) {γ τ : Path a b} (h : range γ = range τ) :
    ∮ z in γ, f z = ∮ z in τ, f z := by

  sorry

-- Differentiable version
theorem goal1 {s : Set ℂ} (h : ∀ x ∈ I, DifferentiableAt ℝ γ.extend x) (F : ℂ → ℂ)
    (hf : ∀ z ∈ s, HasDerivAt F (f z) z) (hint : PathIntegrable f γ)
    (himg : Set.range γ ⊆ s) :
    ∮ z in γ, f z = F b - F a := by
  rw [goal0]
  calc
  _ = (F ∘ γ.extend) 1 - (F ∘ γ.extend) 0 := by
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ hint]
    intro x hx
    apply HasDerivAt.comp
    · apply hf
      apply himg
      aesop
    rw [hasDerivAt_deriv_iff]
    aesop
  _ = _ := by grind

-- Piecewise C1 version, do as sum over pieces of differentiable version
theorem goal1' {s : Set ℂ} (h : γ.IsPiecewiseC1) (F : ℂ → ℂ)
    (hf : ∀ z ∈ s, HasDerivAt F (f z) z) (hint : PathIntegrable f γ)
    (himg : Set.range γ ⊆ s) :
    ∮ z in γ, f z = F b - F a := by
  sorry

--maybe use HasDerivWithIn?
theorem goal2 {s : Set ℂ} {γ : Path a a} (h : γ.IsPiecewiseC1) (hs : SimplyConnectedSpace s)
    (F : ℂ → ℂ) (hf : ∀ z ∈ s, HasDerivAt F (f z) z) (hint : PathIntegrable f γ)
    (himg : Set.range γ ⊆ s) :
    ∮ z in γ, f z = 0 := by
  rw [goal1' (F := F) (h := by assumption) (hf := hf) (hint := hint) (himg := himg)]
  rw [sub_self]

--convex
theorem goal3 (s : Set ℂ) (hs : SimplyConnectedSpace s) (hf : DifferentiableOn ℂ f s) :
    Complex.IsExactOn f s := by
  sorry

theorem goal4 (s : Set ℂ) (γ : Path a a) (h : γ.IsPiecewiseC1)
    (hs : SimplyConnectedSpace s) (hf : DifferentiableOn ℂ f s)
    (hint : PathIntegrable f γ) (himg : Set.range γ ⊆ s) :
    ∮ z in γ, f z = 0 := by
  have : Complex.IsExactOn f s := by
    apply goal3 _ _ hs hf
  obtain ⟨F, hF⟩ := this
  apply goal2 <;> assumption
