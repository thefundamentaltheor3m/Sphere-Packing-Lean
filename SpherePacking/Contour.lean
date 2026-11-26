module

public import Mathlib

@[expose] public noncomputable section

open unitInterval Set Complex Real MeasureTheory

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
  IntervalIntegrable (f ∘ γ.extend) volume 0 1

abbrev Path.IsPiecewiseC1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : E}
    (γ : Path a b) : Prop :=
  IsPiecewise γ fun p ↦ ContDiffOn ℝ 1 p.extend I

/-- The contour integral `∫_γ f(z) dz`, i.e. the curve integral of the 1-form
`ω z = (v ↦ f z * v)`. -/
noncomputable abbrev contourIntegral {a b : ℂ} (f : ℂ → ℂ) (γ : Path a b) : ℂ :=
  curveIntegral (fun z ↦ ContinuousLinearMap.lsmul ℂ ℂ (f z)) γ

notation3 "∮ "(...)" in "γ", "r:60:(scoped f => contourIntegral f γ) => r

variable {a b c : ℂ} (f : ℂ → ℂ) (γ : Path a b) (τ : Path b c)

theorem goal0 :  ∮ z in γ, f z = ∫ z in 0..1, f (γ.extend z) * (deriv γ.extend z) := by
  simp [contourIntegral, curveIntegral_eq_intervalIntegral_deriv]

theorem contourIntegral_def : ∮ z in γ, f z =
    curveIntegral (fun z ↦ ContinuousLinearMap.lsmul ℂ ℂ (f z)) γ :=
  rfl
--{E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℂ → E)

--hasDerivAt_circleMap
theorem circleIntegral_eq_contourIntegral (f : ℂ → ℂ) (p : ℂ) (R : ℝ) :
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

theorem contourIntegral_append : ∮ z in γ.trans τ, f z = ∮ z in γ, f z + ∮ z in τ, f z := by
  sorry

--#check contDiffOn

--def IsNice (p : Path a b) : Prop :=
-- Set.piecewise

theorem goal1 {s : Set ℂ} (h : γ.IsPiecewiseC1) (F : ℂ → ℂ) (hs : SimplyConnectedSpace s)
    (hf : ∀ z ∈ s, HasDerivAt F (f z) z) (hint : PathIntegrable f γ) :
    ∮ z in γ, f z = F b - F a := by
  rw [goal0]
  sorry

--maybe use HasDerivWithIn?
theorem goal2 {s : Set ℂ} {γ : Path a a} (h : γ.IsPiecewiseC1) (hs : SimplyConnectedSpace s)
    (F : ℂ → ℂ) (hf : ∀ z ∈ s, HasDerivAt F (f z) z) (hint : PathIntegrable f γ) :
    ∮ z in γ, f z = 0 := by
  rw [goal1 (F := F) (h := by assumption) (hs := hs) (hf := hf) (hint := hint)]
  rw [sub_self]

--convex
theorem goal3 (s : Set ℂ) (hs : SimplyConnectedSpace s) (hf : DifferentiableOn ℂ f s) :
    Complex.IsExactOn f s := by
  sorry

theorem goal4 (s : Set ℂ) (γ : Path a a) (h : γ.IsPiecewiseC1)
    (hs : SimplyConnectedSpace s) (hf : DifferentiableOn ℂ f s) :
    ∮ z in γ, f z = 0 := by
  have : Complex.IsExactOn f s := by
    apply goal3 _ _ hs hf
  obtain ⟨F, hF⟩ := this
  apply goal2 <;> assumption
