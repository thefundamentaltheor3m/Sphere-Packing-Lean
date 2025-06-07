import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.Calculus.ContDiff.Bounds

open SchwartzMap Function RCLike

section SchwartzMap_multidimensional_of_schwartzMap_real

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma hasFDerivAt_norm_sq {x : F} :
  HasFDerivAt (fun x ↦ ‖x‖ ^ 2) (2 • ((innerSL ℝ) x)) x := (hasFDerivAt_id x).norm_sq

lemma differentiableAt_norm_sq {x : F} :
  DifferentiableAt ℝ (fun x ↦ ‖x‖ ^ 2) x := hasFDerivAt_norm_sq.differentiableAt

lemma differentiable_norm_sq :
  Differentiable ℝ (fun (x : F) ↦ ‖x‖ ^ 2) := fun _ => differentiableAt_norm_sq

lemma fderiv_norm_sq {x : F} :
  fderiv ℝ (fun x ↦ ‖x‖ ^ 2) x = 2 • ((innerSL ℝ) x) := hasFDerivAt_norm_sq.fderiv

lemma hasTemperateGrowth_norm_sq :
    HasTemperateGrowth (fun (x :F) ↦ ‖x‖ ^ 2) := by
  refine Function.HasTemperateGrowth.of_fderiv ?_ differentiable_norm_sq (k := 2) (C := 1) ?_
  · convert (2 • (innerSL ℝ)).hasTemperateGrowth
    ext
    simp [fderiv_norm_sq]
  · intro x
    rw [norm_pow, norm_norm, one_mul, sq_le_sq, abs_norm, abs_of_nonneg (by positivity)]
    linear_combination

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] (f : 𝓢(ℝ, ℂ))

@[simps!]
noncomputable def schwartzMap_multidimensional_of_schwartzMap_real : 𝓢(F, ℂ) :=
    f.compCLM ℝ hasTemperateGrowth_norm_sq <| by
  use 1, 1
  intro _
  simp only [norm_pow, norm_norm]
  nlinarith

end SchwartzMap_multidimensional_of_schwartzMap_real

section SchwartzMap_multidimensional_of_schwartzLike_real

open Set

open scoped ContDiff

-- variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {g : ℝ → ℂ} (d : ℕ) (hContDiffOn : ContDiffOn ℝ ∞ g (Ici (0 : ℝ)))
  (hdecay : ∀ k n : ℕ, ∃ C : ℝ, ∀ x ∈ (Ici (0 : ℝ)), ‖x‖ ^ ((k : ℝ) / 2) *
    ‖iteratedFDerivWithin ℝ n g (Ici 0) x‖ ≤ C)

include hContDiffOn in
lemma ContDiffOn.comp_norm_sq_smooth :  -- More general version possible but for now unnecessary
    ContDiff ℝ ∞ (fun (x : EuclideanSpace ℝ (Fin d)) ↦ g (‖x‖ ^ 2)) :=
  hContDiffOn.comp_contDiff (contDiff_norm_sq ℝ) <| by simp

-- To match with `norm_iteratedFDerivWithin_comp_le`
local notation "f" => fun (x : EuclideanSpace ℝ (Fin d)) ↦ ‖x‖ ^ 2
local notation "s" => (⊤ : Set (EuclideanSpace ℝ (Fin d)))
local notation "t" => (Ici (0 : ℝ) : Set ℝ)

private lemma hf : ContDiffOn ℝ ∞ f s := (contDiff_norm_sq ℝ).contDiffOn
private lemma hn (n : ℕ) : n ≤ ∞ := right_eq_inf.mp rfl
private lemma ht : UniqueDiffOn ℝ t := uniqueDiffOn_Ici 0
private lemma hs : UniqueDiffOn ℝ s := uniqueDiffOn_univ
private lemma hst : Set.MapsTo f s t := fun _ _ => by simp

private lemma hD (x : EuclideanSpace ℝ (Fin d)) (n : ℕ) : ∀ i : ℕ, 1 ≤ i → i ≤ n →
    ‖iteratedFDerivWithin ℝ i f s x‖ ≤ 2 ^ i := by
  have hnorm_eq (y : EuclideanSpace ℝ (Fin d)) : ‖y‖ ^ 2 = inner ℝ y y := by
    simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs, PiLp.inner_apply, inner_apply,
      conj_trivial]
    congr; ext; ring
  have hinner_eq_innerSL (a b : EuclideanSpace ℝ (Fin d)) : inner ℝ a b = innerSL ℝ a b := rfl
  intro i hi₁ hi₂
  rw [iteratedFDerivWithin_eq_iteratedFDeriv]
  · have h₁ : ContDiff ℝ ∞ (fun (x : EuclideanSpace ℝ (Fin d)) ↦ x) := contDiff_id
    simp only [hnorm_eq, hinner_eq_innerSL]
    have h₂ : ‖innerSL ℝ‖ ≤ 1 := norm_innerSL_le (E := EuclideanSpace ℝ (Fin d)) ℝ
    have h₃ : i ≤ ∞ := right_eq_inf.mp rfl
    have h₄ :=
      ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one (innerSL ℝ) h₁ h₁ x h₃ h₂
    apply h₄.trans
    have h₅ (j : ℕ) : ‖iteratedFDeriv ℝ j (fun (x : EuclideanSpace ℝ (Fin d)) ↦ x) x‖ = 1 := by
      -- Why is this not obvious?
      sorry
    simp only [h₅, mul_one]
    norm_cast
    rw [Nat.sum_range_choose i]
  · exact uniqueDiffOn_univ
  · exact (contDiff_norm_sq ℝ).contDiffAt
  · trivial

private lemma h_pow (x : EuclideanSpace ℝ (Fin d)) (k : ℕ) :
    (‖x‖ ^ 2) ^ ((k : ℝ) / 2) = ‖x‖ ^ (k : ℝ) := by
  have h_pow_2 : ‖x‖ ^ 2 = ‖x‖ ^ (2 : ℝ) := by norm_cast
  rw [h_pow_2, ← Real.rpow_mul (by positivity)]
  field_simp

include hdecay in
private lemma hC (n k : ℕ) : ∃ C : ℝ, ∀ (x : EuclideanSpace ℝ (Fin d)), ∀ i ≤ n,
    (‖x‖ ^ k) * ‖iteratedFDerivWithin ℝ i g t (f x)‖ ≤ C := by
  -- I know that given some k, for all n, there is a Cₙ such that ‖deriv‖ ≤ Cₙ / (‖x‖ ^ (k / 2))
  -- Simply define C to be the max of all Cᵢ for 0 ≤ i ≤ n
  -- Copilot did the first few lines
  choose! C hC using hdecay k
  let Cmax := Finset.range (n + 1) |>.sup' (by simp) C
  use Cmax
  intro x i hi
  specialize hC i (‖x‖ ^ 2)
  simp only [mem_Ici, norm_nonneg, pow_nonneg, norm_pow, norm_norm, forall_const, h_pow] at hC
  have hCi : C i ≤ Cmax := Finset.le_sup' C <| Finset.mem_range_succ_iff.mpr hi
  simp only
  have := hC.trans hCi
  norm_cast at this

include hContDiffOn in
private lemma hsmooth : ContDiff ℝ ∞ fun (x : EuclideanSpace ℝ (Fin d)) ↦ g (‖x‖ ^ 2) :=
  hContDiffOn.comp_norm_sq_smooth d

noncomputable def schwartzMap_multidimensional_of_schwartzLike_real :
    𝓢(EuclideanSpace ℝ (Fin d), ℂ) where
  toFun := fun x ↦ g (f x)
  smooth' := hsmooth d hContDiffOn
  decay' := by
    intro k n
    obtain ⟨C, hC⟩ := hC d hdecay n k
    use n.factorial * C * 2 ^ n
    intro x
    specialize hC x
    -- specialize hC (‖x‖ ^ 2)
    -- simp only [mem_Ici, norm_nonneg, pow_nonneg, norm_pow, norm_norm, forall_const] at hC
    -- rw [h_pow d x k, Real.rpow_natCast] at hC
    rw [← iteratedFDerivWithin_eq_iteratedFDeriv uniqueDiffOn_univ
      (ContDiff.contDiffAt <| (contDiff_infty.mp (hsmooth d hContDiffOn)) n) (mem_univ x)]
    wlog hk_ne_zero : k ≠ 0
    · simp only [ne_eq, Decidable.not_not] at hk_ne_zero
      simp only [hk_ne_zero, pow_zero, one_mul] at hC ⊢
      exact norm_iteratedFDerivWithin_comp_le hContDiffOn (hf d) (hn n) ht (hs d) (hst d) (x := x)
        (by simp) hC (hD d x n)
    wlog hx_ne_zero : x ≠ 0
    · simp only [ne_eq, Decidable.not_not] at hx_ne_zero
      specialize hC n le_rfl
      rw [hx_ne_zero, norm_zero, zero_pow hk_ne_zero, zero_mul] at hC ⊢
      positivity
    have hx_pos : 0 < ‖x‖ ^ k := by positivity
    have hC' : ∀ i ≤ n,
        ‖iteratedFDerivWithin ℝ i g (Ici 0) ((fun x ↦ ‖x‖ ^ 2) x)‖ ≤ C / (‖x‖ ^ k) := by
      intro i hi
      specialize hC i hi
      rw [mul_comm, ← le_div_iff₀ hx_pos (c := ‖x‖ ^ k) (b := C)] at hC
      exact hC
    conv_lhs => rw [mul_comm]
    rw [← le_div_iff₀ hx_pos (c := ‖x‖ ^ k)]
    have hrearrange : n.factorial * C * 2 ^ n / ‖x‖ ^ k = ↑n.factorial * (C / ‖x‖ ^ k) * 2 ^ n := by
      field_simp
    rw [hrearrange]
    exact norm_iteratedFDerivWithin_comp_le hContDiffOn (hf d) (hn n) ht (hs d) (hst d) (x := x)
      (by simp) hC' (hD d x n)

example (h : ℝ → ℝ) : ContDiff ℝ ∞ h → ∀ n : ℕ, ContDiff ℝ ↑n h := by
  rw [contDiff_infty]
  exact fun h n ↦ h n

example (n d : ℕ) (x : EuclideanSpace ℝ (Fin d)) (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (h : ContDiffOn ℝ n g ⊤) :
    iteratedFDeriv ℝ n g x = iteratedFDerivWithin ℝ n g (⊤ : Set (EuclideanSpace ℝ (Fin d))) x :=
  Eq.symm (iteratedFDerivWithin_eq_iteratedFDeriv uniqueDiffOn_univ (h x trivial) trivial)

end SchwartzMap_multidimensional_of_schwartzLike_real
