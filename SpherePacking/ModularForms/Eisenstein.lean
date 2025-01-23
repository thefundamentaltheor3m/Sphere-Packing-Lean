/-
The purpose of this file is to define the Eisenstein series we are interested in using more
convenient notation. We will also state results with `sorry`s that should be proved and eventually
moved elsewhere in the project.
-/
import Mathlib
import SpherePacking.ModularForms.Cauchylems
import SpherePacking.ModularForms.tendstolems
import SpherePacking.ModularForms.Icc_Ico_lems
import SpherePacking.ModularForms.limunder_lems
import SpherePacking.ModularForms.E2

-- import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

open ArithmeticFunction

noncomputable section Definitions

def standardcongruencecondition : Fin 2 → ZMod ((1 : ℕ+) : ℕ) := 0



-- private lemma aux4 : (3 : ℤ) ≤ 4 := by norm_num
-- private lemma aux6 : (3 : ℤ) ≤ 6 := by norm_num

/- The Eisenstein Series E₂, E₄ and E₆ -/

def E₄ : ModularForm (CongruenceSubgroup.Gamma ↑1) 4 :=
  (1/2 : ℂ) • eisensteinSeries_MF (by norm_num) standardcongruencecondition /-they need  1/2 for the
    normalization to match up (since the sum here is taken over coprime integers).-/
def E (k : ℤ) (hk : 3 ≤ k) : ModularForm (CongruenceSubgroup.Gamma ↑1) k :=
  (1/2 : ℂ) • eisensteinSeries_MF hk standardcongruencecondition /-they need  1/2 for the
    normalization to match up (since the sum here is taken over coprime integers).-/
def E₆ : ModularForm (CongruenceSubgroup.Gamma ↑1) 6 :=
  (1/2 : ℂ) • eisensteinSeries_MF (by norm_num) standardcongruencecondition

lemma E4_apply (z : ℍ) : E₄ z = E 4 (by norm_num) z := rfl

lemma E6_apply (z : ℍ) : E₆ z = E 6 (by norm_num) z := rfl

instance natPosSMul : SMul ℕ+ ℍ where
  smul x z := UpperHalfPlane.mk (x * z) <| by simp; apply z.2

theorem natPosSMul_apply (c : ℕ+) (z : ℍ) : ((c  • z : ℍ) : ℂ) = (c : ℂ) * (z : ℂ) := by rfl


theorem nat_pos_tprod2' {α : Type*} [TopologicalSpace α] [CommMonoid α]  (f : ℕ → α) :
    (Multipliable fun x : ℕ+ => f x) ↔ Multipliable  fun x : ℕ => f (x + 1) :=
  by
  rw [← Equiv.multipliable_iff _root_.Equiv.pnatEquivNat]
  constructor
  intro hf
  apply Multipliable.congr hf
  intro b
  simp
  intro hf
  apply Multipliable.congr hf
  intro b
  simp


variable (f : ℍ → ℂ) (k : ℤ) (z : ℍ)


/-this is being PRd-/
lemma Complex.summable_nat_multipliable_one_add (f : ℕ → ℂ) (hf : Summable f)
    (hff : ∀ n : ℕ, 1 + f n ≠ 0) : Multipliable (fun n : ℕ => 1 + f n) := by sorry

/- lemma MultipliableDiscriminantProductExpansion (z : ℍ) :
  Multipliable (fun  (n : ℕ+) => (1 - cexp (2 * π * Complex.I * n * z)) ^ 24) := by
  sorry --dont seem to need this -/

theorem term_ne_zero (z : ℍ) (n : ℕ) : 1 -cexp (2 * ↑π * Complex.I * (↑n + 1) * ↑z) ≠ 0 := by
  rw [@sub_ne_zero]
  intro h
  have :=  exp_upperHalfPlane_lt_one_nat z n
  rw [← h] at this
  simp only [AbsoluteValue.map_one, lt_self_iff_false] at *


lemma MultipliableEtaProductExpansion (z : ℍ) :
    Multipliable (fun (n : ℕ) => (1 - cexp (2 * π * Complex.I * (n + 1) * z)) ) := by
  have := Complex.summable_nat_multipliable_one_add (fun (n : ℕ) => (-cexp (2 * π * Complex.I * (n + 1) * z)) ) ?_ ?_
  simp at this
  apply this.congr
  intro n
  ring
  rw [←summable_norm_iff]
  simpa using summable_exp_pow z
  intro n
  simp
  apply term_ne_zero

lemma MultipliableEtaProductExpansion_pnat (z : ℍ) :
  Multipliable (fun (n : ℕ+) => (1 - cexp (2 * π * Complex.I * n * z))) := by
  conv =>
    enter [1]
    ext n
    rw [sub_eq_add_neg]
  let g := (fun (n : ℕ) => (1 - cexp (2 * π * Complex.I * n * z)) )
  have := MultipliableEtaProductExpansion z
  conv at this =>
    enter [1]
    ext n
    rw [show (n : ℂ) + 1 = (((n + 1) : ℕ) : ℂ) by simp]
  rw [← nat_pos_tprod2' g ] at this
  apply this.congr
  intro b
  rfl

/-this is being PRd-/
lemma prod_tendstoUniformlyOn_tprod' {α : Type*} [TopologicalSpace α] {f : ℕ → α → ℂ} (K : Set α)
    (hK : IsCompact K) (u : ℕ → ℝ) (hu : Summable u) (h : ∀ n x, x ∈ K → (‖(f n x)‖) ≤ u n)
    (hfn : ∀ x : K, ∀ n : ℕ, 1 + f n x ≠ 0) (hcts : ∀ n, ContinuousOn (fun x => (f n x)) K) :
    TendstoUniformlyOn (fun n : ℕ => fun a : α => ∏ i in Finset.range n, (1 + (f i a)))
    (fun a => ∏' i, (1 + (f i a))) atTop K := by sorry

/- variable {ι κ α : Type*}
variable [Preorder α] [CommMonoid α] [TopologicalSpace α] {a c : α} {f : ι → α}

@[to_additive]
theorem le_hasProd_of_le_prod_ev [ClosedIciTopology α]
    (hf : HasProd f a) (h : ∀ᶠ s : Finset ι in atTop, c ≤ ∏ i ∈ s, f i)  : c ≤ a :=
  ge_of_tendsto hf h

@[to_additive]
theorem le_hasProd_of_le_prod_ev_range [ClosedIciTopology α] [T2Space α] (f : ℕ → α) (hm : Multipliable f)
    (hf : HasProd f a) (h : ∀ᶠ s : ℕ in atTop, c ≤ ∏ i ∈ Finset.range s, f i)  : c ≤ a := by
  rw [Multipliable.hasProd_iff_tendsto_nat hm] at hf
  apply ge_of_tendsto hf h -/


/-Being Prd-/
lemma Complex.log_of_summable {f : ℕ → ℂ} (hf : Summable f) :
    Summable (fun n : ℕ => Complex.log (1 + f n)) := by sorry

lemma tprod_ne_zero (x : ℍ) (f : ℕ → ℍ → ℂ) (hf : ∀ i x, 1 + f i x ≠ 0)
  (hu : ∀ x : ℍ, Summable fun n => f n x) : (∏' i : ℕ, (1 + f i) x) ≠ 0 := by
  have := Complex.cexp_tsum_eq_tprod (fun n => 1 + f n x) ?_ ?_
  simp
  rw [← this]
  simp only [comp_apply, exp_ne_zero, not_false_eq_true]
  intro n
  simp
  apply hf
  simp
  apply Complex.log_of_summable
  apply hu x


/- theorem logDeriv_tprod_eq_tsumb  {s : Set ℂ} (hs : IsOpen s) (x : s) (f : ℕ → ℂ → ℂ)
    (hf : ∀ i, f i x ≠ 0)
    (hd : ∀ i : ℕ, DifferentiableOn ℂ (f i) s) (hm : Summable fun i ↦ logDeriv (f i) ↑x)
    (htend :TendstoLocallyUniformlyOn (fun n ↦ ∏ i ∈ Finset.range n, f i)
    (fun x ↦ ∏' (i : ℕ), f i x) atTop s) (hnez : ∏' (i : ℕ), f i ↑x ≠ 0) :
    logDeriv (∏' i : ℕ, f i ·) x = ∑' i : ℕ, logDeriv (f i) x := by
    rw [← Complex.cexp_tsum_eq_tprod]
    rw [logDeriv]
    simp
    rw [deriv_comp]
    simp
    rw [deriv_tsum ]
    simp
    congr
    ext n


    all_goals{sorry} -/

theorem logDeriv_tprod_eq_tsum  {s : Set ℂ} (hs : IsOpen s) (x : s) (f : ℕ → ℂ → ℂ)
    (hf : ∀ i, f i x ≠ 0)
    (hd : ∀ i : ℕ, DifferentiableOn ℂ (f i) s) (hm : Summable fun i ↦ logDeriv (f i) ↑x)
    (htend : TendstoLocallyUniformlyOn (fun n ↦ ∏ i ∈ Finset.range n, f i)
    (fun x ↦ ∏' (i : ℕ), f i x) atTop s) (hnez : ∏' (i : ℕ), f i ↑x ≠ 0) :
    logDeriv (∏' i : ℕ, f i ·) x = ∑' i : ℕ, logDeriv (f i) x := by
    have h2 := Summable.hasSum hm
    rw [Summable.hasSum_iff_tendsto_nat hm] at h2
    apply symm
    rw [← Summable.hasSum_iff hm]
    rw [Summable.hasSum_iff_tendsto_nat hm]
    let g := (∏' i : ℕ, f i ·)
    have := logDeriv_tendsto (fun n ↦ ∏ i ∈ Finset.range n, (f i)) g (s := s) hs (p := atTop)
    simp only [eventually_atTop, ge_iff_le, ne_eq, forall_exists_index, Subtype.forall, g] at this
    have HT := this x x.2 ?_ ?_ ?_ ?_
    conv =>
      enter [1]
      ext n
      rw [← logDeriv_prod _ _ _ (by intro i hi; apply hf i)
        (by intro i hi; apply (hd i x x.2).differentiableAt; exact IsOpen.mem_nhds hs x.2)]
    apply HT.congr
    intro m
    congr
    ext i
    simp only [Finset.prod_apply]
    exact htend
    use 0
    intro b hb
    rw [DifferentiableOn]
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    have hp : ∀ (i : ℕ), i ∈ Finset.range b →  DifferentiableAt ℂ (f i) z := by
      intro i hi
      have := (hd i z hz).differentiableAt
      apply this
      exact IsOpen.mem_nhds hs hz
    have := DifferentiableAt.finset_prod hp
    convert this
    simp only [Finset.prod_apply]
    · exact hnez




    --DifferentiableAt.finset_prod
    --logDeriv_tendsto

    --Summable.hasSum_iff_tendsto_nat



/-
lemma MultipliableDiscriminantProductExpansion2 : Multipliable (fun (z : UpperHalfPlane) =>
  cexp (2 * π * Complex.I * z) * ∏' (n : ℕ+), (1 - cexp (2 * π * Complex.I * n * z)) ^ 24) := by
    --I dont think we mean this
    sorry -/


/- /- The eta function. Best to define it on all of ℂ since we want to take its logDeriv. -/
def η (z : ℂ) := cexp (2 * π * Complex.I * z / 24) * ∏' (n : ℕ+),
    (1 - cexp (2 * π * Complex.I * n * z)) -/

/- The eta function. Best to define it on all of ℂ since we want to take its logDeriv. -/
def η (z : ℂ) := cexp (2 * π * Complex.I * z / 24) * ∏' (n : ℕ),
    (1 - cexp (2 * π * Complex.I * (n + 1) * z))

lemma aux47 (r : ℂ) (hr : ‖r‖ < 1) : Tendsto (fun n : ℕ => 1 - r^n) atTop (𝓝 1) := by
  rw [show (1 : ℂ) = 1 - 0 by ring]
  apply Filter.Tendsto.sub
  simp
  apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr

lemma logDeriv_one_sub_exp (r : ℂ) : logDeriv (fun z => 1 - r * cexp (z)) =
    fun z => -r * cexp z / (1 - r * cexp ( z)) := by
  ext z
  rw [logDeriv]
  simp only [Pi.div_apply, differentiableAt_const, differentiableAt_exp, DifferentiableAt.mul,
    deriv_sub, deriv_const', deriv_mul, zero_mul, Complex.deriv_exp, zero_add, zero_sub, neg_mul]

lemma logDeriv_one_sub_exp_comp (r : ℂ) (g : ℂ → ℂ) (hg : Differentiable ℂ g) :
    logDeriv ((fun z => 1 - r * cexp (z)) ∘ g) =
    fun z => -r * ((deriv g) z) * cexp (g z) / (1 - r * cexp (g (z))) := by
  ext y
  rw  [logDeriv_comp, logDeriv_one_sub_exp]
  simp only [neg_mul]
  ring
  simp only [differentiableAt_const, differentiableAt_exp, DifferentiableAt.mul,
    DifferentiableAt.sub]
  exact hg y

lemma logDeriv_q_expo_summable (r : ℂ) (hr : ‖r‖ < 1) : Summable fun n : ℕ =>
    (n * r^n / (1 - r^n)) := by
  have := aux47 r hr
  have h1 : Tendsto (fun n : ℕ => (1 : ℂ)) atTop (𝓝 1) := by simp
  have h2 := Filter.Tendsto.div h1 this (by simp)
  rw [Metric.tendsto_atTop] at h2
  simp only [gt_iff_lt, ge_iff_le, Pi.div_apply, one_div, ne_eq, one_ne_zero, not_false_eq_true,
    div_self, dist_eq_norm] at h2
  have h3 := h2 1 (by norm_num)
  apply Summable.of_norm_bounded_eventually_nat (fun n => 2 * ‖n * r^n‖)
  apply Summable.mul_left
  simp
  · have := (summable_norm_pow_mul_geometric_of_norm_lt_one 1 hr)
    simp at this
    apply this
  · simp
    obtain ⟨N, hN⟩ := h3
    use N
    intro n hn
    have h4 := hN n hn
    have := norm_lt_of_mem_ball h4 (E := ℂ)
    simp at *
    rw [div_eq_mul_inv]
    rw [mul_comm]
    gcongr
    apply le_trans this.le
    norm_cast

lemma eta_tndntunif : TendstoLocallyUniformlyOn (fun n ↦ ∏ x ∈ Finset.range n,
    fun x_1 ↦ 1 + -cexp (2 * ↑π * Complex.I *  (↑x + 1) * x_1))
    (fun x ↦ ∏' (i : ℕ), (1 + -cexp (2 * ↑π * Complex.I * (↑i + 1) * x))) atTop {x | 0 < x.im} := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact]
  intro K hK hK2
  by_cases hN : ¬ Nonempty K
  rw [@not_nonempty_iff_eq_empty'] at hN
  rw [hN]
  exact tendstoUniformlyOn_empty
  have hc : ContinuousOn (fun x ↦ ‖cexp (2 * ↑π * Complex.I * x)‖) K := by
    fun_prop
  have := IsCompact.exists_sSup_image_eq_and_ge hK2 (by simpa using hN) hc
  obtain ⟨z, hz, hB, HB⟩ := this
  have :=  prod_tendstoUniformlyOn_tprod'  K  hK2 (f := (fun i ↦
    fun x_1 ↦ -cexp (2 * ↑π * Complex.I *  (i + 1) * x_1)))
    (fun n=> ‖cexp (2 * ↑π * Complex.I * z)^(n + 1)‖) ?_ ?_ ?_ ?_
  simp at *
  convert this
  simp only [Finset.prod_apply]
  · simp_rw [norm_pow]
    rw [summable_nat_add_iff 1]
    simp only [norm_eq_abs, summable_geometric_iff_norm_lt_one, Real.norm_eq_abs, Complex.abs_abs]
    apply  exp_upperHalfPlane_lt_one ⟨z, by simpa using (hK hz)⟩
  · intro n
    intro x hx
    simp only [norm_neg]
    rw [show 2 * ↑π * Complex.I * (↑n + 1) * x = (n+1)* (2 * ↑π * Complex.I  * x) by ring ]
    rw [show (n : ℂ) + 1 = (((n + 1) : ℕ) : ℂ) by simp]
    rw [Complex.exp_nat_mul]
    have HB2 := HB x hx
    simp_rw [norm_pow]
    apply pow_le_pow_left₀ _  HB2
    simp only [norm_eq_abs, apply_nonneg]
  · intro x k
    simpa using term_ne_zero ⟨x.1, by simpa using (hK x.2)⟩ k
  · intro n
    fun_prop
  · apply (isOpen_lt continuous_const Complex.continuous_im)

theorem eta_tprod_ne_zero (z : ℍ) :
  ∏' (n : ℕ), (1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * ↑z)) ≠ 0 := by
  simp_rw [sub_eq_add_neg]
  have := tprod_ne_zero z (fun n x => -cexp (2 * ↑π * Complex.I * (n + 1) * x)) ?_ ?_
  simp only [Pi.add_apply, Pi.one_apply, ne_eq] at *
  apply this
  intro i x
  simpa using (term_ne_zero x i)
  intro x
  rw [←summable_norm_iff]
  simpa using summable_exp_pow x

lemma eta_nonzero_on_UpperHalfPlane (z : ℍ) : η z ≠ 0 := by
  rw [η]
  have := eta_tprod_ne_zero z
  simp at *
  apply this

lemma tsum_eq_tsum_sigma (z : ℍ) : ∑' n : ℕ,
    (n + 1) * cexp (2 * π * Complex.I * (n + 1) * z) / (1 - cexp (2 * π *  Complex.I * (n + 1) * z)) =
    ∑' n : ℕ, sigma 1 (n + 1) * cexp (2 * π * Complex.I * (n + 1) * z) := by
  have :=  fun m : ℕ => tsum_choose_mul_geometric_of_norm_lt_one  (r := (cexp (2 * ↑π * Complex.I * ↑z))^(m+1)) 0 (by rw [← exp_aux]; simpa using exp_upperHalfPlane_lt_one_nat z m)
  simp only [add_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, zero_add, pow_one,
    one_div] at this
  conv =>
    enter [1,1]
    ext n
    rw [show (n : ℂ) + 1 = (((n + 1) : ℕ) : ℂ) by simp only [Nat.cast_add, Nat.cast_one],
      exp_aux, div_eq_mul_one_div]
    simp
    rw [← this n, ← tsum_mul_left]
    conv =>
      enter [1]
      ext m
      rw [mul_assoc, ← pow_succ' (cexp (2 * ↑π * Complex.I * ↑z) ^ (n + 1)) m ]
  have := tsum_sigma_eqn z (k := 1)
  conv =>
    enter [2,1]
    ext n
    rw [show (n : ℂ) + 1 = (((n + 1) : ℕ) : ℂ) by simp]
  have h1 := tsum_pnat_eq_tsum_succ3 (fun n => sigma 1 (n) * cexp (2 * π * Complex.I * (n) * z))
  simp only [UpperHalfPlane.coe] at *
  rw [← h1]
  have h2 := fun n : ℕ => tsum_pnat_eq_tsum_succ3
    ( fun m => ↑(n + 1) * (cexp (2 * ↑π * Complex.I * ↑z) ^ (n + 1)) ^ (m))
  simp only [UpperHalfPlane.coe] at h2
  conv =>
    enter [1,1]
    ext n
    rw [show (n : ℂ) + 1 = (((n + 1) : ℕ) : ℂ) by simp only [Nat.cast_add, Nat.cast_one], ← h2 n]
    conv =>
      enter [1]
      ext m
      rw [pow_right_comm]
  have h3 := tsum_pnat_eq_tsum_succ3
      (fun n ↦ ∑' (m : ℕ+), ↑(n) * (cexp (2 * ↑π * Complex.I * ↑z) ^ (m : ℕ)) ^ (n))
  simp only [UpperHalfPlane.coe] at h3
  rw [← h3, ← this]
  simp only [pow_one]
  rw [tsum_prod' ]
  congr
  ext n
  congr
  ext m
  simp only [mul_eq_mul_left_iff, Nat.cast_eq_zero, PNat.ne_zero, or_false]
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  congr 1
  ring
  · have := a4 2 z
    apply this.congr
    intro b
    simp only [uncurry, Nat.add_one_sub_one, pow_one, UpperHalfPlane.coe, mul_eq_mul_left_iff,
      Nat.cast_eq_zero, PNat.ne_zero, or_false]
    ring_nf
  · intro e
    have := a1  2 e z
    simpa using this

/--This we should get from the modular forms repo stuff. Will port these things soon. -/
lemma E₂_eq (z : UpperHalfPlane) : E₂ z =
    1 - 24 * ∑' (n : ℕ+),
    ↑n * cexp (2 * π * Complex.I * n * z) / (1 - cexp (2 * π * Complex.I * n * z)) := by
  rw [E₂]
  simp
  rw [G2_q_exp]
  rw [mul_sub]
  congr 1
  · rw [riemannZeta_two]
    have hpi : (π : ℂ) ≠ 0 := by simp; exact Real.pi_ne_zero
    field_simp
    ring
  · rw [← mul_assoc]
    congr 1
    · rw [riemannZeta_two]
      have hpi : (π : ℂ) ≠ 0 := by simp; exact Real.pi_ne_zero
      norm_cast
      field_simp
      ring
    · have hl := tsum_pnat_eq_tsum_succ3 (fun n => sigma 1 n * cexp (2 * π * Complex.I * n * z))
      have hr := tsum_pnat_eq_tsum_succ3 (fun n => n * cexp (2 * π * Complex.I * n * z) / (1 - cexp (2 * π * Complex.I * n * z)))
      rw [hl, hr]
      have ht := tsum_eq_tsum_sigma z
      simp at *
      rw [ht]

lemma tsum_log_deriv_eqn (z : ℍ) :
  ∑' (i : ℕ), logDeriv (fun x ↦ 1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x)) ↑z  =  ∑' n : ℕ,
    -(2 * ↑π * Complex.I * (↑n + 1)) * cexp (2 * π * Complex.I * (n + 1) * z) / (1 - cexp (2 * π *  Complex.I * (n + 1) * z)) := by
  congr
  ext i
  have h0 : ∀ i : ℕ, Differentiable ℂ (fun x => (2 * π * Complex.I * (i + 1) * x)) := by
      intro i
      fun_prop
  have h1 := fun i : ℕ => logDeriv_one_sub_exp_comp 1 (fun x => (2 * π * Complex.I * (i + 1) * x)) (h0 i)
  have h2 : ∀ i : ℕ, (fun x ↦ 1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x))=
      ((fun z ↦ 1 - 1 * cexp z) ∘ fun x ↦ 2 * ↑π * Complex.I * (↑i + 1) * x) := by
      intro i
      ext y
      simp
  have h3 : ∀ i : ℕ, deriv (fun x : ℂ => (2 * π * Complex.I * (i + 1) * x)) =
        fun _ => 2 * (π : ℂ) * Complex.I * (i + 1) := by
      intro i
      ext y
      rw [deriv_mul]
      · simp only [differentiableAt_const, deriv_mul, deriv_const', zero_mul, mul_zero, add_zero,
        deriv_add, deriv_id'', mul_one, zero_add]
      · simp only [differentiableAt_const]
      · simp only [differentiableAt_id']
  rw [h2 i, h1 i, h3 i]
  simp

lemma logDeriv_z_term (z : ℍ) : logDeriv (fun z ↦ cexp (2 * ↑π * Complex.I * z / 24)) ↑z  = 2* ↑π * Complex.I / 24 := by
  have : (fun z ↦ cexp (2 * ↑π * Complex.I * z / 24)) = (fun z ↦ cexp (z)) ∘ (fun z => (2 * ↑π * Complex.I / 24) * z)  := by
    ext y
    simp
    congr
    ring
  rw [this, logDeriv_comp, deriv_const_mul]
  simp only [LogDeriv_exp, Pi.one_apply, deriv_id'', mul_one, one_mul]
  · fun_prop
  · fun_prop
  · fun_prop

theorem eta_differentiableAt (z : ℍ) :
  DifferentiableAt ℂ (fun z ↦ ∏' (n : ℕ), (1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * z))) ↑z := by
  have hD := eta_tndntunif.differentiableOn ?_ ?_
  simp_rw [sub_eq_add_neg]
  rw [DifferentiableOn] at hD
  have hDz := (hD z (by apply z.2)).differentiableAt
  apply hDz
  · apply IsOpen.mem_nhds  (isOpen_lt continuous_const Complex.continuous_im)
    apply z.2
  · simp
    use 0
    intro b hb
    have := DifferentiableOn.finset_prod (u := Finset.range b)
      (f := fun i : ℕ => fun x => 1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x))
      (s := {x : ℂ | 0 < x.im}) ?_
    · apply this.congr
      intro x hx
      simp [sub_eq_add_neg]
    · intro i hi
      fun_prop
  · apply isOpen_lt continuous_const Complex.continuous_im

lemma eta_DifferentiableAt_UpperHalfPlane (z : ℍ) : DifferentiableAt ℂ η z := by
  unfold η
  apply DifferentiableAt.mul
  · conv =>
      enter [2]
      rw [show (fun z => cexp (2 * ↑π * Complex.I * z / 24)) = cexp ∘ (fun z => 2 * ↑π * Complex.I * z / 24) by rfl]
    apply DifferentiableAt.cexp
    fun_prop
  · apply eta_differentiableAt

lemma eta_logDeriv (z : ℍ) : logDeriv η z = (π * Complex.I / 12) * E₂ z := by
  unfold η
  rw [logDeriv_mul]
  have HG := logDeriv_tprod_eq_tsum (s := {x : ℂ | 0 < x.im}) ?_ z
    (fun (n : ℕ) => fun (x : ℂ) => 1 - cexp (2 * π * Complex.I * (n + 1) * x)) ?_ ?_ ?_ ?_ ?_
  simp only [mem_setOf_eq, UpperHalfPlane.coe] at *
  rw [HG]
  · have := tsum_log_deriv_eqn z
    have h0 := logDeriv_z_term z
    simp only [UpperHalfPlane.coe] at *
    rw [this, E₂, h0]
    simp
    rw [G2_q_exp]
    rw [riemannZeta_two]
    conv =>
      enter [1,2,1]
      ext n
      rw [show  -(2 * ↑π * Complex.I * (↑n + 1) * cexp (2 * ↑π * Complex.I * (↑n + 1) * z.1)) /
        (1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * z.1)) =
        (-2 * ↑π * Complex.I) * (((↑n + 1) * cexp (2 * ↑π * Complex.I * (↑n + 1) * z.1)) /
        (1 - cexp (2 * ↑π * Complex.I * (n + 1) * z.1))) by ring]
    rw [tsum_mul_left (a := -2 * ↑π * Complex.I)]
    have := tsum_eq_tsum_sigma z
    simp only [UpperHalfPlane.coe] at *
    rw [this, mul_sub]
    rw [sub_eq_add_neg, mul_add]
    congr 1
    · have hpi : (π : ℂ) ≠ 0 := by simpa using Real.pi_ne_zero
      ring_nf
      field_simp
      ring
    · ring_nf
      rw [show ↑π * Complex.I * (1 / 12) *
        -((↑π ^ 2 * (1 / 6))⁻¹ * (1 / 2) * (↑π ^ 2 * 8 *
        ∑' (n : ℕ+), ↑((σ 1) ↑n) * cexp (↑π * Complex.I * 2 * ↑↑n * z.1))) =
        (↑π * Complex.I * (1 / 12) * -((↑π ^ 2 * (1 / 6))⁻¹ * (1 / 2) * (↑π ^ 2 * 8)) *
        ∑' (n : ℕ+), ↑((σ 1) ↑n) * cexp (↑π * Complex.I * 2 * ↑↑n * z.1)) by ring]
      congr 1
      have hpi : (π : ℂ) ≠ 0 := by simpa using Real.pi_ne_zero
      field_simp
      ring
      conv =>
        enter [1,1]
        ext n
        rw [show (n : ℂ) + 1 = (((n + 1) : ℕ) : ℂ) by simp]
      have hl := tsum_pnat_eq_tsum_succ3
        (fun n ↦ ↑((σ 1) (n)) * cexp (↑π * Complex.I * 2 * (↑n) * ↑z))
      simp only [UpperHalfPlane.coe] at hl
      rw [← hl]
  · exact isOpen_lt continuous_const Complex.continuous_im
  · intro i
    simp only [mem_setOf_eq, ne_eq]
    rw [@sub_eq_zero]
    intro h
    have j := exp_upperHalfPlane_lt_one_nat z i
    simp only [UpperHalfPlane.coe] at *
    rw [← h] at j
    simp at j
  · intro i x hx
    fun_prop
  · simp only [mem_setOf_eq]
    have h0 : ∀ i : ℕ, Differentiable ℂ (fun x => (2 * π * Complex.I * (i + 1) * x)) := by
      intro i
      fun_prop
    have h1 := fun i : ℕ => logDeriv_one_sub_exp_comp 1 (fun x => (2 * π * Complex.I * (i + 1) * x)) (h0 i)
    have h2 : ∀ i : ℕ, (fun x ↦ 1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x))=
      ((fun z ↦ 1 - 1 * cexp z) ∘ fun x ↦ 2 * ↑π * Complex.I * (↑i + 1) * x) := by
      intro i
      ext y
      simp
    have h3 : ∀ i : ℕ, deriv (fun x : ℂ => (2 * π * Complex.I * (i + 1) * x)) =
        fun _ => 2 * (π : ℂ) * Complex.I * (i + 1) := by
      intro i
      ext y
      rw [deriv_mul]
      · simp only [differentiableAt_const, deriv_mul, deriv_const', zero_mul, mul_zero, add_zero,
        deriv_add, deriv_id'', mul_one, zero_add]
      · simp only [differentiableAt_const]
      · simp only [differentiableAt_id']
    conv =>
      enter [1]
      ext i
      rw [h2 i, h1 i, h3 i]
    simp only [neg_mul, one_mul]
    conv =>
      enter [1]
      ext i
      rw [mul_assoc, neg_div, ← mul_div]
    apply Summable.neg
    apply Summable.mul_left
    have hS := logDeriv_q_expo_summable (cexp (2 * ↑π * Complex.I * ↑z))
      (by simpa only [norm_eq_abs] using exp_upperHalfPlane_lt_one z)
    rw [← summable_nat_add_iff 1] at hS
    apply hS.congr
    intro b
    congr
    simp only [Nat.cast_add, Nat.cast_one]
    · rw [← Complex.exp_nsmul]
      simp only [UpperHalfPlane.coe, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring_nf
    · rw [← Complex.exp_nsmul]
      simp only [UpperHalfPlane.coe, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring_nf
  · simp_rw [sub_eq_add_neg]
    apply eta_tndntunif
  · exact eta_tprod_ne_zero z
  · simp only [ne_eq, exp_ne_zero, not_false_eq_true]
  · exact eta_tprod_ne_zero z
  · fun_prop
  · apply eta_differentiableAt


end Definitions

noncomputable section Holomorphicity

-- Try and get the desired holomorphicity results for φ₀, φ₂ and φ₄ in terms of the Eᵢ

end Holomorphicity

noncomputable section Integrability

-- Here, we show that

end Integrability

open Complex Real

lemma deriv_eq_iff (f g : ℂ → ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    deriv f = deriv g ↔ ∃z, f = g + (fun _ => z) := by
  constructor
  intro h
  rw [← sub_eq_zero] at h
  have h0 := fun z => congrFun h z
  simp only [Pi.sub_apply, Pi.zero_apply] at *
  have h2 := is_const_of_deriv_eq_zero (f := f - g)
  simp only [Pi.sub_apply] at *
  use f 1 - g 1
  ext x
  simp only [Pi.add_apply]
  have h43 := h2 ?_ ?_ x 1
  rw [← h43]
  simp only [add_sub_cancel]
  apply Differentiable.sub hf hg
  · intro t
    have h1 :=  deriv_sub (f := f) (g := g) (x := t) ?_ ?_
    have h2 := h0 t
    rw [← h2]
    have h3 : f - g = fun y => f y - g y := by rfl
    rw [h3]
    exact h1
    · exact hf.differentiableAt (x := t)
    · exact hg.differentiableAt (x := t)
  intro h
  obtain ⟨z, hz⟩ := h
  rw [hz]
  have ht : g + (fun _ => z) = fun x => g x + (fun _ => z) x := by rfl
  rw [ht]
  simp only [deriv_add_const']

lemma func_div_ext (a b c d : ℂ → ℂ) (hb : ∀ x, b x ≠ 0) (hd : ∀ x, d x ≠ 0) :
     a / b = c /d ↔ a * d = b * c := by
  constructor
  intro h
  have h0 := fun z => congrFun h z
  simp only [Pi.sub_apply, Pi.zero_apply] at *
  ext x
  have h1 := h0 x
  simp only [Pi.div_apply] at h1
  have e1 := hb x
  have e2 := hd x
  simp only [Pi.mul_apply]
  rw [div_eq_div_iff] at h1
  nth_rw 2 [mul_comm]
  exact h1
  exact e1
  exact e2
  intro h
  ext x
  simp only [Pi.div_apply]
  rw [div_eq_div_iff]
  have hj := congrFun h x
  simp only [Pi.mul_apply] at hj
  nth_rw 2 [mul_comm]
  exact hj
  apply hb x
  apply hd x

lemma func_div (a b c d : ℂ → ℂ) (x : ℂ) (hb : b x ≠ 0) (hd :  d x ≠ 0) :
     (a / b) x = (c /d) x ↔ (a * d) x = (b * c) x := by
  constructor
  intro h
  simp only [Pi.sub_apply, Pi.zero_apply] at *
  simp only [Pi.mul_apply]
  simp only [Pi.div_apply] at h
  rw [div_eq_div_iff] at h
  nth_rw 2 [mul_comm]
  exact h
  exact hb
  exact hd
  intro h
  simp only [Pi.div_apply]
  rw [div_eq_div_iff]
  simp only [Pi.mul_apply] at h
  nth_rw 2 [mul_comm]
  exact h
  apply hb
  apply hd


lemma deriv_EqOn_congr {f g : ℂ → ℂ} (s : Set ℂ) (hfg : s.EqOn f g) (hs : IsOpen s) :
    s.EqOn (deriv f) ( deriv g) := by
  intro x hx
  rw [← derivWithin_of_isOpen hs hx]
  rw [← derivWithin_of_isOpen hs hx]
  apply derivWithin_congr hfg
  apply hfg hx

lemma logDeriv_eqOn_iff (f g : ℂ → ℂ) (s : Set ℂ) (hf : DifferentiableOn ℂ f s)
    (hg : DifferentiableOn ℂ g s) (hs : s.Nonempty) (hs2 : IsOpen s) (hsc : Convex ℝ s)
    (hgn : ∀ x, x ∈ s →  g x ≠ 0) (hfn : ∀ x, x ∈ s → f x ≠ 0) : EqOn (logDeriv f) (logDeriv g) s ↔
    ∃( z : ℂ),  z ≠ 0 ∧  EqOn (f) (z • g) s := by
  constructor
  simp_rw [logDeriv]
  intro h
  rw [@nonempty_def] at hs
  obtain ⟨t, ht⟩ := hs
  use (f t) * (g t)⁻¹
  refine ⟨by apply mul_ne_zero (hfn t ht) (by simpa using (hgn t ht)) , ?_⟩
  intro y hy
  have h2 := h hy
  rw [func_div] at h2
  have hderiv : EqOn (deriv (f * g⁻¹))  (deriv f * g⁻¹ - f * deriv g / g ^ 2) s := by
    have hfg : f * g⁻¹ = fun x => f x * (g⁻¹ x) := by rfl
    rw [hfg]
    intro z hz
    rw [deriv_mul]
    have hgi : g⁻¹ = (fun x => x⁻¹) ∘ g := by
      ext y
      simp only [Pi.inv_apply, comp_apply]
    rw [hgi, deriv_comp, deriv_inv]
    simp only [comp_apply, neg_mul, mul_neg, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
    ring
    · refine differentiableAt_inv ?_
      exact hgn z hz
    · apply hg.differentiableAt (x := z) (IsOpen.mem_nhds hs2 hz)
    · exact hf.differentiableAt (x := z) (IsOpen.mem_nhds hs2 hz)
    · apply DifferentiableAt.inv
      exact hg.differentiableAt (x := z) (IsOpen.mem_nhds hs2 hz)
      exact hgn z hz
  have H3 := Convex.is_const_of_fderivWithin_eq_zero (f := f * g⁻¹) (𝕜 := ℂ) (s := s) ?_ ?_ ?_ hy ht
  simp only [Pi.mul_apply, Pi.inv_apply] at H3
  rw [← H3]
  field_simp [hgn y hy]
  · exact hsc
  · apply DifferentiableOn.mul
    exact hf
    apply DifferentiableOn.inv
    exact hg
    exact hgn
  have he : s.EqOn  (deriv f * g⁻¹ - f * deriv g / g ^ 2)  0 := by
    intro z hz
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.inv_apply, Pi.div_apply, Pi.pow_apply, Pi.zero_apply]
    have hgg : g z ≠ 0 := by apply hgn z hz
    field_simp
    rw [pow_two, mul_comm, mul_assoc, ← mul_sub]
    simp only [mul_eq_zero]
    right
    have H := h hz
    rw [func_div] at H
    simp only [Pi.mul_apply] at H
    rw [← H]
    ring
    exact hfn z hz
    exact hgn z hz
  intro v hv
  have H := h hv
  rw [func_div] at H
  have ha := hderiv hv
  have hb := he hv
  rw [hb] at ha
  simp only [Pi.zero_apply] at ha
  rw [fderivWithin_of_isOpen hs2 hv]
  exact Eq.symm (ContinuousLinearMap.ext_ring (_root_.id (Eq.symm ha)))
  exact  hfn v hv
  exact  hgn v hv
  exact  hfn y hy
  exact hgn y hy
  · intro h
    obtain ⟨z, hz0, hz⟩ := h
    intro x hx
    have h := hz hx
    simp_rw [logDeriv_apply]
    have HJ := deriv_EqOn_congr s hz hs2 hx
    rw [HJ, h]
    nth_rw 1 [show z • g = fun x => z • g x by rfl]
    rw [deriv_const_smul]
    simp
    rw [mul_div_mul_left (deriv g x) (g x) hz0]
    exact hg.differentiableAt (x := x) (IsOpen.mem_nhds hs2 hx)


noncomputable def csqrt : ℂ → ℂ :=  (fun a : ℂ => cexp ((1 / (2 : ℂ))* (log a)))

lemma csqrt_deriv (z : ℍ) : deriv (fun a : ℂ => cexp ((1 / (2 : ℂ))* (log a))) z =
    (2 : ℂ)⁻¹ • (fun a : ℂ => cexp (-(1 / (2 : ℂ)) * (log a))) z:= by
  have :  (fun a ↦ cexp (1 / 2 * Complex.log a)) =  cexp ∘ (fun a ↦ (1 / 2 * Complex.log a)) := by
    ext z
    simp
  have hzz : ↑z ∈ slitPlane := by
    rw [@mem_slitPlane_iff]
    right
    have hz := z.2
    simp only [UpperHalfPlane.coe] at hz
    exact Ne.symm (ne_of_lt hz)
  rw [this, deriv_comp]
  simp
  rw [Complex.exp_neg]
  field_simp
  rw [show cexp (Complex.log ↑z / 2) * deriv Complex.log ↑z * (2 * cexp (Complex.log ↑z / 2)) =
    cexp (Complex.log ↑z / 2) * (cexp (Complex.log ↑z / 2)) * 2 * deriv Complex.log ↑z by ring]
  rw [← Complex.exp_add]
  ring_nf
  rw [Complex.exp_log]
  have hl := (Complex.hasDerivAt_log (z := z) hzz).deriv
  rw [hl]
  field_simp [ne_zero z]
  · apply ne_zero z
  · fun_prop
  · apply DifferentiableAt.const_mul
    refine Complex.differentiableAt_log hzz

lemma csqrt_differentiableAt (z : ℍ) : DifferentiableAt ℂ csqrt z := by
  unfold csqrt
  apply DifferentiableAt.cexp
  apply DifferentiableAt.const_mul
  apply Complex.differentiableAt_log
  rw [@mem_slitPlane_iff]
  right
  have hz := z.2
  simp only [UpperHalfPlane.coe] at hz
  exact Ne.symm (ne_of_lt hz)

lemma eta_logDeriv_eql (z : ℍ) : (logDeriv (η ∘ (fun z : ℂ => -1/z))) z =
  (logDeriv ((csqrt) * η)) z := by
  have h0 : (logDeriv (η ∘ (fun z : ℂ => -1/z))) z = ((z :ℂ)^(2 : ℤ))⁻¹ * (logDeriv η) (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ) := by
    rw [logDeriv_comp, mul_comm]
    congr
    conv =>
      enter [1,1]
      intro z
      rw [neg_div]
      simp
    simp only [deriv.neg', deriv_inv', neg_neg, inv_inj]
    norm_cast
    · simpa only using
      eta_DifferentiableAt_UpperHalfPlane (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ)
    conv =>
      enter [2]
      ext z
      rw [neg_div]
      simp
    apply DifferentiableAt.neg
    apply DifferentiableAt.inv
    simp only [differentiableAt_id']
    exact ne_zero z
  rw [h0, show ((csqrt) * η) = (fun x => (csqrt) x * η x) by rfl, logDeriv_mul]
  nth_rw 2 [logDeriv_apply]
  unfold csqrt
  have := csqrt_deriv z
  rw [this]
  simp only [one_div, neg_mul, smul_eq_mul]
  nth_rw 2 [div_eq_mul_inv]
  rw [← Complex.exp_neg, show 2⁻¹ * cexp (-(2⁻¹ * Complex.log ↑z)) * cexp (-(2⁻¹ * Complex.log ↑z)) =
   (cexp (-(2⁻¹ * Complex.log ↑z)) * cexp (-(2⁻¹ * Complex.log ↑z)))* 2⁻¹ by ring, ← Complex.exp_add,
   ← sub_eq_add_neg, show -(2⁻¹ * Complex.log ↑z) - 2⁻¹ * Complex.log ↑z = -Complex.log ↑z by ring, Complex.exp_neg, Complex.exp_log, eta_logDeriv z]
  have Rb := eta_logDeriv (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ)
  simp only [coe_mk_subtype] at Rb
  rw [Rb]
  have E := E₂_transform z
  simp only [one_div, neg_mul, smul_eq_mul, SL_slash, slash_def, slash, ← ModularGroup.sl_moeb,
    modular_S_smul, ModularGroup.det_coe, ofReal_one, Int.reduceSub, zpow_one, mul_one,
    ModularGroup.denom_S, Int.reduceNeg, zpow_neg] at *
  have h00 :  (UpperHalfPlane.mk (-z : ℂ)⁻¹ z.im_inv_neg_coe_pos) = (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ) := by
    simp [UpperHalfPlane.mk]
    ring_nf
  rw [h00] at E
  rw [← mul_assoc, mul_comm, ← mul_assoc]
  simp only [UpperHalfPlane.coe] at *
  rw [E, add_mul, add_comm]
  congr 1
  have hzne := ne_zero z
  have hI : Complex.I ≠ 0 := by
    exact I_ne_zero
  have hpi : (π : ℂ) ≠ 0 := by
    simp only [ne_eq, ofReal_eq_zero]
    exact pi_ne_zero
  simp [UpperHalfPlane.coe] at hzne ⊢
  field_simp
  ring
  rw [mul_comm]
  · simpa only [UpperHalfPlane.coe, ne_eq] using (ne_zero z)
  · simp only [csqrt, one_div, ne_eq, Complex.exp_ne_zero, not_false_eq_true]
  · apply eta_nonzero_on_UpperHalfPlane z
  · unfold csqrt
    rw [show (fun a ↦ cexp (1 / 2 * Complex.log a)) = cexp ∘ (fun a ↦ 1 / 2 * Complex.log a) by rfl]
    apply DifferentiableAt.comp
    simp
    apply DifferentiableAt.const_mul
    apply Complex.differentiableAt_log
    rw [@mem_slitPlane_iff]
    right
    have hz := z.2
    simp only [UpperHalfPlane.coe] at hz
    exact Ne.symm (ne_of_lt hz)
  · apply eta_DifferentiableAt_UpperHalfPlane z

lemma eta_logderivs : {z : ℂ | 0 < z.im}.EqOn (logDeriv (η ∘ (fun z : ℂ => -1/z)))
  (logDeriv ((csqrt) * η)) := by
  intro z hz
  have := eta_logDeriv_eql ⟨z, hz⟩
  exact this

lemma eta_logderivs_const : ∃ z : ℂ, z ≠ 0 ∧ {z : ℂ | 0 < z.im}.EqOn ((η ∘ (fun z : ℂ => -1/z)))
  (z • ((csqrt) * η)) := by
  have h := eta_logderivs
  rw [logDeriv_eqOn_iff] at h
  · exact h
  · apply DifferentiableOn.comp
    pick_goal 4
    · use ({z : ℂ | 0 < z.im})
    · rw [DifferentiableOn]
      intro x hx
      apply DifferentiableAt.differentiableWithinAt
      apply eta_DifferentiableAt_UpperHalfPlane ⟨x, hx⟩
    · apply DifferentiableOn.div
      fun_prop
      fun_prop
      intro x hx
      have hx2 := ne_zero (⟨x, hx⟩ : ℍ)
      norm_cast at *
    · intro y hy
      simp
      have := UpperHalfPlane.im_inv_neg_coe_pos (⟨y, hy⟩ : ℍ)
      conv =>
        enter [2,1]
        rw [neg_div]
        rw [div_eq_mul_inv]
        simp
      simp at *
      rw [neg_div, neg_neg_iff_pos]
      exact this
  · apply DifferentiableOn.mul
    simp only [DifferentiableOn, mem_setOf_eq]
    intro x hx
    apply (csqrt_differentiableAt ⟨x, hx⟩).differentiableWithinAt
    simp only [DifferentiableOn, mem_setOf_eq]
    intro x hx
    apply (eta_DifferentiableAt_UpperHalfPlane ⟨x, hx⟩).differentiableWithinAt
  · use UpperHalfPlane.I
    simp only [coe_I, mem_setOf_eq, Complex.I_im, zero_lt_one]
  · exact isOpen_lt continuous_const Complex.continuous_im
  · exact convex_halfSpace_im_gt 0
  · intro x hx
    simp only [Pi.mul_apply, ne_eq, mul_eq_zero, not_or]
    refine ⟨ ?_ , by apply eta_nonzero_on_UpperHalfPlane ⟨x, hx⟩⟩
    unfold csqrt
    simp only [one_div, Complex.exp_ne_zero, not_false_eq_true]
  · intro x hx
    simp only [comp_apply, ne_eq]
    have := eta_nonzero_on_UpperHalfPlane ⟨-1 / x, by simpa using pnat_div_upper 1 ⟨x, hx⟩⟩
    simpa only [ne_eq, coe_mk_subtype] using this

lemma csqrt_I : (csqrt (Complex.I)) ^ 24  = 1 := by
  unfold csqrt
  rw [← Complex.exp_nat_mul]
  conv =>
    enter [1,1]
    rw [← mul_assoc]
    rw [show ((24 : ℕ) : ℂ) * (1 / 2) = (12 : ℕ) by
      field_simp; ring]
  rw [Complex.exp_nat_mul]
  rw [Complex.exp_log]
  have hi4 := Complex.I_pow_four
  have : Complex.I ^ 12 = (Complex.I ^ 4) ^ 3 :=by
    rw [← @npow_mul]
  rw [this, hi4]
  simp
  exact I_ne_zero

lemma csqrt_pow_24 (z : ℂ) (hz : z ≠ 0) : (csqrt z) ^ 24 = z ^ 12 := by
  unfold csqrt
  rw [← Complex.exp_nat_mul]
  conv =>
    enter [1,1]
    rw [← mul_assoc]
    rw [show ((24 : ℕ) : ℂ) * (1 / 2) = (12 : ℕ) by
      field_simp; ring]
  rw [Complex.exp_nat_mul, Complex.exp_log hz]


lemma eta_equality : {z : ℂ | 0 < z.im}.EqOn ((η ∘ (fun z : ℂ => -1/z)))
   ((csqrt (Complex.I))⁻¹ • ((csqrt) * η)) := by
  have h := eta_logderivs_const
  obtain ⟨z, hz, h⟩ := h
  intro x hx
  have h2 := h hx
  have hI : (Complex.I) ∈ {z : ℂ | 0 < z.im} := by
    simp only [mem_setOf_eq, Complex.I_im, zero_lt_one]
  have h3 := h hI
  simp at h3
  conv at h3 =>
    enter [2]
    rw [← mul_assoc]
  have he : η Complex.I ≠ 0 := by
    have h:=  eta_nonzero_on_UpperHalfPlane UpperHalfPlane.I
    convert h
  have hcd := (mul_eq_right₀ he).mp (_root_.id (Eq.symm h3))
  rw [mul_eq_one_iff_inv_eq₀ hz] at hcd
  rw [@inv_eq_iff_eq_inv] at hcd
  rw [hcd] at h2
  exact h2

noncomputable section  Product_Formula


/- The discriminant form -/
def Δ (z : UpperHalfPlane) :=  cexp (2 * π * Complex.I * z) * ∏' (n : ℕ),
    (1 - cexp (2 * π * Complex.I * (n + 1) * z)) ^ 24

lemma DiscriminantProductFormula ( z : ℍ) : Δ z =  cexp (2 * π * Complex.I * z) * ∏' (n : ℕ+),
    (1 - cexp (2 * π * Complex.I * (n) * z)) ^ 24 := by
    simp [Δ]
    conv =>
      enter [1,1]
      ext n
      rw [show (n : ℂ) + 1 = ((n + 1) : ℕ) by simp]

    have := tprod_pnat_eq_tprod_succ (fun n => (1 - cexp (2 * π * Complex.I * (n) * z)) ^ 24)
    rw [this]


lemma Multipliable_pow (f : ℕ → ℂ) (hf : Multipliable f) (n : ℕ) :
     Multipliable (fun i => f i ^ n) := by
  induction' n with n hn
  · simp
    apply multipliable_one
  · conv =>
      enter [1]
      intro u
      rw [pow_succ]
    apply Multipliable.mul hn hf

lemma tprod_pow (f : ℕ → ℂ) (hf : Multipliable f) (n : ℕ) : (∏' (i : ℕ), f i) ^ n = ∏' (i : ℕ), (f i) ^ n := by
  induction' n with n hn
  · simp
  · rw [pow_succ]
    rw [hn]
    rw [← tprod_mul]
    congr
    apply Multipliable_pow f hf n
    exact hf

lemma Delta_eq_eta_pow (z : ℍ) : Δ z = (η z) ^ 24 := by
  rw [η, Δ, mul_pow]
  congr
  rw [← Complex.exp_nat_mul]
  congr 1
  field_simp
  rw [tprod_pow]
  apply MultipliableEtaProductExpansion



/- φ₀, φ₋₂ and φ₋₄, except we can't use - signs in subscripts for definitions... -/
def φ₀ (z : ℍ) := (((E₂ z) * (E₄ z) - (E₆ z)) ^ 2) / (Δ z)
def φ₂' (z : ℍ) := (E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) / (Δ z)
def φ₄' (z : ℍ) := ((E₄ z) ^ 2) / (Δ z)
/- We extend these definitions to ℂ for convenience. -/
def φ₀'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₀ ⟨z, hz⟩ else 0
def φ₂'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₂' ⟨z, hz⟩ else 0
def φ₄'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₄' ⟨z, hz⟩ else 0


/-This should be easy from the definition and the Mulitpliable bit. -/
lemma Δ_ne_zero (z : UpperHalfPlane) : Δ z ≠ 0 := by
  rw [Delta_eq_eta_pow]
  simpa using eta_nonzero_on_UpperHalfPlane z



/-This one is easy.-/
lemma Discriminant_T_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.T) = Δ := by
  ext z
  rw [ modular_slash_T_apply, Δ, Δ]
  simp only [coe_vadd, ofReal_one]
  have h1 : cexp (2 * ↑π * Complex.I * (1 + ↑z)) = cexp (2 * ↑π * Complex.I * (↑z)) := by
    simpa using exp_periodo z 1
  rw [h1]
  simp only [mul_eq_mul_left_iff, Complex.exp_ne_zero, or_false]
  apply tprod_congr
  intro b
  have := exp_periodo z (b+1)
  simp only [Nat.cast_add, Nat.cast_one] at this
  rw [this]


/-This is the hard one. -/
lemma Discriminant_S_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.S) = Δ := by
  ext z
  rw [ modular_slash_S_apply, Delta_eq_eta_pow, Delta_eq_eta_pow]
  have he := eta_equality z.2
  simp only [comp_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, UpperHalfPlane.coe_mk,
    Int.reduceNeg, zpow_neg] at *
  have hi :  -1/(z.1 : ℂ) = (-(z : ℂ))⁻¹ := by
    rw [neg_div]
    rw [← neg_inv]
    simp [UpperHalfPlane.coe]
  rw [hi] at he
  rw [he, mul_pow, mul_pow, inv_pow, csqrt_I]
  simp only [inv_one, one_mul, UpperHalfPlane.coe]
  rw [mul_comm]
  have hzz := csqrt_pow_24 z.1 (ne_zero z)
  rw [hzz, ← mul_assoc]
  have hz := ne_zero z
  simp only [UpperHalfPlane.coe, ne_eq] at hz
  norm_cast
  field_simp

-- use E₂_transform

/-this is from other file-/
theorem slashaction_generators_SL2Z
    (f : ℍ → ℂ) (k : ℤ) (hS : f ∣[k] ModularGroup.S = f) (hT : f ∣[k] ModularGroup.T = f) :
    (∀ γ : SL(2, ℤ), f ∣[k] γ = f) := by sorry

def Discriminant_SIF : SlashInvariantForm (CongruenceSubgroup.Gamma 1) 12 where
  toFun := Δ
  slash_action_eq' A := by
    intro hA
    exact slashaction_generators_SL2Z Δ 12 (Discriminant_S_invariant) (Discriminant_T_invariant) A

open Manifold in

instance : atImInfty.NeBot := by
  rw [atImInfty, Filter.comap_neBot_iff ]
  simp only [mem_atTop_sets, ge_iff_le, forall_exists_index]
  intro t x hx
  have := ENNReal.nhdsGT_ofNat_neBot
  let z : ℂ := Complex.mk (0 : ℝ) (|x| + 1)
  have h0 : 0 ≤ |x| := by
    apply abs_nonneg
  have hz : 0 < z.im := by
    positivity
  use ⟨z, hz⟩
  apply hx
  simp only [UpperHalfPlane.im, coe_mk_subtype]
  have : x ≤ |x| := by
    apply le_abs_self
  apply le_trans this
  simp only [le_add_iff_nonneg_right, zero_le_one, z]


lemma arg_pow_aux (n : ℕ) (x : ℂ) (hx : x ≠ 0) (hna : |arg x| < π / n) :
  Complex.arg (x ^ n) = n * Complex.arg x := by
  induction' n with n hn2
  simp only [pow_zero, arg_one, CharP.cast_eq_zero, zero_mul]
  by_cases hn0 : n = 0
  · simp only [hn0, zero_add, pow_one, Nat.cast_one, one_mul]
  · rw [pow_succ, arg_mul, hn2, Nat.cast_add]
    ring
    apply lt_trans hna
    gcongr
    exact (lt_add_one n)
    apply pow_ne_zero n hx
    exact hx
    simp only [mem_Ioc]
    rw [hn2]
    rw [abs_lt] at hna
    constructor
    · have hnal := hna.1
      rw [← neg_div] at hnal
      rw [div_lt_iff₀' ] at hnal
      · rw [@Nat.cast_add, add_mul] at hnal
        simpa only [gt_iff_lt, Nat.cast_one, one_mul] using hnal
      · norm_cast
        omega
    · have hnal := hna.2
      rw [lt_div_iff₀', Nat.cast_add] at hnal
      · rw [add_mul] at hnal
        simpa only [ge_iff_le, Nat.cast_one, one_mul] using hnal.le
      · norm_cast
        omega
    apply lt_trans hna
    gcongr
    exact (lt_add_one n)

lemma one_add_abs_half_ne_zero {x : ℂ} (hb : Complex.abs x < 1 / 2) : 1 + x ≠ 0 := by
  by_contra h
  rw [@add_eq_zero_iff_neg_eq] at h
  rw [← h] at hb
  simp at hb
  linarith

lemma arg_pow (n : ℕ) (f : ℕ → ℂ) (hf : Tendsto f atTop (𝓝 0)) : ∀ᶠ m : ℕ in atTop,
    Complex.arg ((1 + f m) ^ n) = n * Complex.arg (1 + f m) := by
  simp only [eventually_atTop, ge_iff_le]
  have hf1 := hf.const_add 1
  simp only [add_zero] at hf1
  have h2 := (Complex.continuousAt_arg (x := 1) ?_)
  rw [ContinuousAt] at *
  have h3 := h2.comp hf1
  simp only [arg_one] at h3
  rw [Metric.tendsto_nhds] at *
  simp only [gt_iff_lt, dist_zero_right, Complex.norm_eq_abs, eventually_atTop, ge_iff_le,
    dist_self_add_left, arg_one, Real.norm_eq_abs, comp_apply] at *
  by_cases hn0 : n = 0
  · rw [hn0]
    simp only [pow_zero, arg_one, CharP.cast_eq_zero, zero_mul, implies_true, exists_const]
  · have hpi : 0 < π / n := by
      apply div_pos
      exact pi_pos
      simp only [Nat.cast_pos]
      omega
    obtain ⟨a, hA⟩ := h3 (π / n) hpi
    obtain ⟨a2, ha2⟩ := hf (1/2) (one_half_pos)
    use max a a2
    intro b hb
    rw [arg_pow_aux n (1 + f b) ?_]
    apply hA b
    exact le_of_max_le_left hb
    have ha2 := ha2 b (le_of_max_le_right hb)
    simp only [ne_eq]
    apply one_add_abs_half_ne_zero ha2
  simp only [one_mem_slitPlane]

lemma arg_pow2 (n : ℕ) (f : ℍ → ℂ) (hf : Tendsto f atImInfty (𝓝 0)) : ∀ᶠ m : ℍ in atImInfty,
    Complex.arg ((1 + f m) ^ n) = n * Complex.arg (1 + f m) := by
  rw [Filter.eventually_iff_exists_mem ]
  have hf1 := hf.const_add 1
  simp only [add_zero] at hf1
  have h2 := (Complex.continuousAt_arg (x := 1) ?_)
  rw [ContinuousAt] at *
  have h3 := h2.comp hf1
  simp only [arg_one] at h3
  rw [Metric.tendsto_nhds] at *
  simp only [gt_iff_lt, dist_zero_right, Complex.norm_eq_abs, eventually_atTop, ge_iff_le,
    dist_self_add_left, arg_one, Real.norm_eq_abs, comp_apply] at *
  by_cases hn0 : n = 0
  · simp_rw [hn0]
    simp only [pow_zero, arg_one, CharP.cast_eq_zero, zero_mul, implies_true, and_true]
    rw [atImInfty]
    simp only [mem_comap, mem_atTop_sets, ge_iff_le]
    use {n  | 1 ≤ n.im}
    use {r : ℝ | 1 ≤ r}
    refine ⟨?_, ?_⟩
    use 1
    intro b hb
    aesop
    simp only [preimage_setOf_eq, subset_refl]
  · have hpi : 0 < π / n := by
      apply div_pos
      exact pi_pos
      simp only [Nat.cast_pos]
      omega
    have hA1 := h3 (π / n) hpi
    have hA2 := hf (1/2) (one_half_pos)
    rw [Filter.eventually_iff_exists_mem ] at hA1 hA2
    obtain ⟨a, ha1, hA1⟩ := hA1
    obtain ⟨a2, ha2, hA2⟩ := hA2
    use min a a2
    refine ⟨by rw [atImInfty] at *; simp at *; refine ⟨ha1, ha2⟩, ?_⟩
    intro b hb
    rw [arg_pow_aux n (1 + f b) ?_]
    apply hA1 b
    exact mem_of_mem_inter_left hb
    have ha2 := hA2 b ( mem_of_mem_inter_right hb)
    simp only [ne_eq]
    apply one_add_abs_half_ne_zero ha2
  simp only [one_mem_slitPlane]

lemma clog_pow (n : ℕ) (f : ℕ → ℂ) (hf : Tendsto f atTop (𝓝 0)) : ∀ᶠ m : ℕ in atTop,
    Complex.log ((1 + f m) ^ n) = n * Complex.log (1 + f m) := by
  have h := arg_pow n f hf
  simp at *
  simp_rw [Complex.log]
  obtain ⟨a, ha⟩ := h
  use a
  intro b hb
  have h2 := ha b hb
  rw [h2]
  simp only [AbsoluteValue.map_pow, log_pow, ofReal_mul, ofReal_natCast]
  ring

lemma clog_pow2 (n : ℕ) (f : ℍ → ℂ) (hf : Tendsto f atImInfty (𝓝 0)) : ∀ᶠ m : ℍ in atImInfty,
    Complex.log ((1 + f m) ^ n) = n * Complex.log (1 + f m) := by
  have h := arg_pow2 n f hf
  simp at *
  simp_rw [Complex.log]
  obtain ⟨a, ha0, ha⟩ := h
  use a
  refine ⟨ha0, ?_⟩
  intro b hb
  have h2 := ha hb
  simp only [mem_atTop_sets, ge_iff_le, mem_preimage, mem_setOf_eq, AbsoluteValue.map_pow, log_pow,
    ofReal_mul, ofReal_natCast] at *
  rw [h2]
  simp only [AbsoluteValue.map_pow, log_pow, ofReal_mul, ofReal_natCast]
  ring


lemma log_summable_pow (f : ℕ → ℂ)  (hf : Summable f)  (m : ℕ) :
    Summable (fun n => Complex.log ((1 + f n)^m)) := by
  have hfl := log_of_summable hf
  have := (Summable.mul_left m (f := (fun n => Complex.log (1 + f n))) hfl).norm
  apply Summable.of_norm_bounded_eventually_nat _ this
  have hft := hf.tendsto_atTop_zero
  have H := clog_pow m f hft
  simp only [norm_mul, Complex.norm_natCast, Complex.norm_eq_abs, eventually_atTop, ge_iff_le] at *
  obtain ⟨a, ha⟩ := H
  use a
  intro b hb
  apply le_of_eq
  rw [ha b hb]
  simp only [AbsoluteValue.map_mul, abs_natCast]


/-
lemma tendstozero_mul_bounded (f g : ℍ → ℂ) (r : ℝ) (hf : Tendsto f atImInfty (𝓝 0)) (hg : ∀ z, ‖g z‖ ≤ r) :
  Tendsto (fun z => f z * g z) atImInfty (𝓝 0) := by
  rw [Metric.tendsto_nhds] at *
  simp only [dist_zero_right, comp_apply] at *
  by_cases hr : r = 0
  · rw [hr] at hg
    simp at hg
    sorry
  intro ε hε
  have hrp : 0 < r := by

    sorry
  have hf2 := hf (ε / r) (div_pos hε hrp)
  rw [Filter.eventually_iff_exists_mem ] at *
  obtain ⟨a, ha0, ha⟩ := hf2
  use a
  refine ⟨ha0, ?_⟩
  intro b hb
  have haa := ha b hb
  rw [norm_mul]
  have hbg := hg b
  have := mul_lt_mul' hbg haa (norm_nonneg (f b)) hrp
  rw [mul_comm]
  convert this
  field_simp -/


lemma tendstozero_mul_bounded2 (f g : ℍ → ℂ) (r : ℝ) (hr : 0 < r) (hf : Tendsto f atImInfty (𝓝 0))
   (hg : ∀ᶠ z in atImInfty, ‖g z‖ ≤ r) :
  Tendsto (fun z => f z * g z) atImInfty (𝓝 0) := by
  rw [Metric.tendsto_nhds] at *
  simp only [dist_zero_right, comp_apply] at *
  intro ε hε
  have hf2 := hf (ε / r) (div_pos hε hr)
  rw [Filter.eventually_iff_exists_mem ] at *
  obtain ⟨a, ha0, ha⟩ := hf2
  obtain ⟨a2, ha2, hA2⟩ := hg
  use min a a2
  refine ⟨by rw [atImInfty] at *; simp at *; refine ⟨ha0, ha2⟩, ?_⟩
  intro b hb
  have haa := ha b (by exact mem_of_mem_inter_left hb)
  have hbg:= hA2 b (by exact mem_of_mem_inter_right hb)
  rw [norm_mul]
  have := mul_lt_mul' hbg haa (by exact norm_nonneg (f b)) hr
  rw [mul_comm]
  convert this
  field_simp

theorem tendsto_neg_cexp_atImInfty (k : ℕ) :
  Tendsto (fun x : ℍ ↦ -cexp (2 * ↑π * Complex.I * (↑k + 1) * ↑x)) atImInfty (𝓝 0) := by
  have := Tendsto.neg (f :=  (fun x : ℍ ↦ cexp (2 * ↑π * Complex.I * (↑k + 1) * ↑x)))
    (l := atImInfty) (y := 0)
  simp only [neg_zero] at this
  apply this
  refine tendsto_exp_nhds_zero_iff.mpr ?_
  simp
  apply Filter.Tendsto.const_mul_atTop
  positivity
  exact tendsto_iff_comap.mpr fun ⦃U⦄ a ↦ a

theorem log_one_neg_cexp_tendto_zero (k : ℕ) :
  Tendsto (fun x : ℍ ↦ Complex.log ((1 - cexp (2 * ↑π * Complex.I * (↑k + 1) * ↑x)) ^ 24))
    atImInfty (𝓝 0) := by
  have : (fun x : ℍ ↦ Complex.log ((1 - cexp (2 * ↑π * Complex.I * (↑k + 1) * ↑x)) ^ 24)) =
     (Complex.log) ∘ ( (fun x => x ^ 24) ∘ (fun x : ℍ ↦((1 - cexp (2 * ↑π * Complex.I * (↑k + 1) * ↑x))))) :=by
     ext x
     simp
  rw [this]
  apply Tendsto.comp (y := 𝓝 1)
  · nth_rw 1 [← Complex.log_one]
    refine ContinuousAt.tendsto (x := 1) (f := Complex.log) ?_
    apply continuousAt_clog
    simp
  · apply Tendsto.comp (y := 𝓝 1)
    refine Continuous.tendsto' ?_ ( 1 : ℂ) (1 : ℂ) ?_
    exact continuous_pow 24
    simp
    simp_rw [sub_eq_add_neg]
    nth_rw 3 [show (1 : ℂ) = 1 + 0 by ring]
    apply Tendsto.add
    simp
    apply tendsto_neg_cexp_atImInfty

variable  {a a₁ a₂ : ℝ}

@[to_additive]
theorem hasProd_le_nonneg (f g : ℕ → ℝ) (h : ∀ i, f i ≤ g i)  (h0 : ∀ i, 0 ≤ f i)
  (hf : HasProd f a₁) (hg : HasProd g a₂) : a₁ ≤ a₂ := by
  apply le_of_tendsto_of_tendsto' hf hg
  intro s
  apply Finset.prod_le_prod
  intros i hi
  exact h0 i
  intros i hi
  exact h i

@[to_additive]
theorem HasProd.le_one_nonneg (g : ℕ → ℝ) (h : ∀ i, g i ≤ 1) (h0 : ∀ i, 0 ≤ g i)
    (ha : HasProd g a) : a ≤ 1 := by
  apply hasProd_le_nonneg (f := g) (g := fun _ => 1) h h0 ha hasProd_one

@[to_additive]
theorem one_le_tprod_nonneg (g : ℕ → ℝ) (h : ∀ i, g i ≤ 1) (h0 : ∀ i, 0 ≤ g i)  : ∏' i, g i ≤ 1 := by
  by_cases hg : Multipliable g
  · apply hg.hasProd.le_one_nonneg g h h0
  · rw [tprod_eq_one_of_not_multipliable hg]
/-
lemma tprod_eventually_bounded (g : ℕ → ℝ) (h : ∀ᶠ i in atTop, g i ≤ 1) (h0 : ∀ i, 0 ≤ g i) :
  ∃ C : ℝ, ∏' i, g i ≤ C := by
  --have := tprod_le_of_prod_range_le (α := ℝ)

  sorry -/

/-
lemma tendsto_prod_of_dominated_convergence {α β G : Type*} {𝓕 : Filter ℍ}
    {f : ℕ → ℍ → ℝ} {g : ℕ → ℝ}
    (hab : ∀ k : ℕ, Tendsto (f k ·)  𝓕 (𝓝 (g k)))
    (h_bound : TendstoLocallyUniformly (fun n ↦ ∏ i ∈ Finset.range n, fun x ↦ f i x)
    (fun x : ℍ ↦ ∏' (i : ℕ), f i x) atTop) :
    Tendsto (∏' k, f k ·) 𝓕 (𝓝 (∏' k, g k)) := by
    --have := TendstoLocallyUniformly.tendsto_comp (F := fun n ↦ ∏ i ∈ Finset.range n, fun x ↦ f x i) (f := (fun x : ℍ ↦ ∏' (i : ℕ), f x i)) (g := g)
    --have h2 := h_bound.comp
    have hh : Multipliable f := by sorry
    have h2 := hh.hasProd
    rw [hh.hasProd_iff_tendsto_nat] at h2
    have ht : Tendsto (fun x => fun n ↦ ∏ i ∈ Finset.range n, f i x) 𝓕 (𝓝 ((fun n ↦ ∏ i ∈ Finset.range n, g n))) := by sorry
    have hg : Multipliable g := by sorry
    have h3 := hg.hasProd
    rw [hg.hasProd_iff_tendsto_nat] at h3

    rw [Metric.tendsto_nhds] at *
    rw [Metric.tendstoLocallyUniformly_iff] at *
    conv at hab =>
      enter [2]
      rw [Metric.tendsto_nhds]
    simp at *

    sorry -/



/- theorem extracted_rre7 :
  Tendsto (fun x : ℍ ↦ ∏' (n : ℕ), (1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * ↑x)) ^ 24) atImInfty (𝓝 1) := by
  have ht : ∀ k : ℕ, Tendsto (fun x : ℍ ↦ ((1 - cexp (2 * ↑π * Complex.I * (↑k + 1) * ↑x)) ^ 24)) atImInfty (𝓝 1) := by
    sorry
  have hmultipliable : ∀ x : ℍ, Multipliable (fun k : ℕ => (1 - cexp (2 * ↑π * Complex.I * (↑k + 1) * x)) ^ 24) := by
    sorry
  have hbound : TendstoLocallyUniformly (fun n ↦ ∏ i ∈ Finset.range n, fun x : ℍ ↦ (1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x)) ^ 24)
      (fun x : ℍ ↦ ∏' (i : ℕ), (1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x)) ^ 24) atTop := by
    sorry
  rw [Metric.tendsto_nhds] at *
  rw [Metric.tendstoLocallyUniformly_iff] at *
  have := hbound 1 (by sorry)
  have hc : Continuous (fun x : ℍ ↦ ∏' (i : ℕ), (1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x)) ^ 24) := by
    sorry
  have hc2 := hc.tendsto

  sorry -/

/- lemma arg_pow_of_le_one (z : ℂ) (n : ℕ) (hz : ‖z‖ < 1) : arg ((1 + z) ^ n) = n * arg (1 + z) := by
  induction' n with n hn
  simp

  sorry -/

lemma I_in_atImInfty (A: ℝ) : { z : ℍ | A ≤ z.im} ∈ atImInfty := by
  rw [atImInfty_mem]
  use A
  simp only [mem_setOf_eq, imp_self, implies_true]

def pnat_smul_stable (S : Set ℍ) := ∀ n : ℕ+, ∀ (s : ℍ), s ∈ S → n • s ∈ S

lemma atImInfy_pnat_mono (S : Set ℍ) (hS : S ∈ atImInfty) (B : ℝ) : ∃ A : ℝ,
    pnat_smul_stable (S ∩ {z : ℍ | max A B ≤ z.im}) ∧ S ∩ {z : ℍ | max A B ≤ z.im} ∈ atImInfty := by
  have hS2 := hS
  rw [atImInfty_mem] at hS
  obtain ⟨A, hA⟩ := hS
  use A
  constructor
  intro n s hs
  simp only [mem_inter_iff, mem_setOf_eq] at *
  have K : max A B ≤ (n • s).im := by
    rw [UpperHalfPlane.im, natPosSMul_apply]
    simp only [mul_im, natCast_re, coe_im, natCast_im, coe_re, zero_mul, add_zero]
    have hs2 := hs.2
    simp at *
    constructor
    apply le_trans hs2.1
    have hn : (1 : ℝ) ≤ n := by
      norm_cast
      exact PNat.one_le n
    apply (le_mul_iff_one_le_left s.2).mpr hn
    apply le_trans hs2.2
    have hn : (1 : ℝ) ≤ n := by
      norm_cast
      exact PNat.one_le n
    apply (le_mul_iff_one_le_left s.2).mpr hn
  refine ⟨?_,?_⟩
  · simp at K
    apply hA _ K.1
  · exact K
  · simp only [ inter_mem_iff, hS2, true_and]
    apply I_in_atImInfty



lemma cexp_two_pi_I_im_antimono (a b : ℍ) (h : a.im ≤ b.im) (n : ℕ) :
    Complex.abs (cexp (2 * ↑π * Complex.I * n * b))
    ≤ Complex.abs (cexp (2 * ↑π * Complex.I *n * a)) := by
  simp_rw [Complex.abs_exp]
  simp
  gcongr


variable {α ι: Type*}

lemma Complex.cexp_tsum_eq_tprod_func (f : ι → α → ℂ) (hfn : ∀ x n, f n x ≠ 0)
    (hf : ∀ x : α, Summable fun n => log (f n x)) :
    (cexp ∘ (fun a : α => (∑' n : ι, log (f n a)))) = fun a : α => ∏' n : ι, f n a := by
  ext a
  apply (HasProd.tprod_eq ?_).symm
  apply ((hf a).hasSum.cexp).congr
  intro _
  congr
  exact funext fun x ↦ exp_log (hfn a x)

theorem Delta_boundedfactor :
  Tendsto (fun x : ℍ ↦ ∏' (n : ℕ), (1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * ↑x)) ^ 24) atImInfty (𝓝 1) := by
  have := Complex.cexp_tsum_eq_tprod_func (fun n : ℕ => fun x : ℍ => (1 - (cexp (2 * ↑π * Complex.I * (↑n + 1) * ↑x))) ^ 24 ) ?_ ?_
  conv =>
    enter [1]
    rw [← this]
  apply Tendsto.comp (y := (𝓝 0))
  refine Continuous.tendsto' ?_ 0 1 ?_
  exact Complex.continuous_exp
  exact Complex.exp_zero
  have := tendsto_tsum_of_dominated_convergence (𝓕 := atImInfty) (g := fun (x : ℕ) => (0 : ℂ))
      (f := (fun x : ℍ ↦ fun (n : ℕ) => Complex.log ((1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * (x : ℂ))) ^ 24)))
      (bound := fun k => Complex.abs (24 *((3/2)* cexp (2 * ↑π * Complex.I * (↑k + 1) * Complex.I))))
  simp at this
  apply this
  · apply Summable.mul_left
    apply Summable.mul_left
    simpa using (summable_exp_pow UpperHalfPlane.I)
  · apply log_one_neg_cexp_tendto_zero
  · have := fun k => (tendsto_neg_cexp_atImInfty k)
    have h0 := this 0
    have h1 := clog_pow2 24 _ h0
    simp only [CharP.cast_eq_zero, zero_add, mul_one, Nat.cast_ofNat] at h1
    rw [Metric.tendsto_nhds] at h0
    have h00 := h0 (1/2) (one_half_pos)
    simp only [CharP.cast_eq_zero, zero_add, mul_one, dist_zero_right, norm_neg,
      Complex.norm_eq_abs, one_div] at h00
    rw [Filter.eventually_iff_exists_mem ] at *
    obtain ⟨a, ha0, ha⟩ := h1
    obtain ⟨a2, ha2, ha3⟩ := h00
    have hminmem: min a a2 ∈ atImInfty := by
      simp only [inf_eq_inter, inter_mem_iff, ha0, ha2, and_self]
    have hT := atImInfy_pnat_mono (min a a2) hminmem 1
    obtain ⟨A, hA, hAmem⟩ := hT
    use (a ⊓ a2) ∩ {z | A ⊔ 1 ≤ z.im}
    refine ⟨hAmem, ?_⟩
    intro b hb k
    let K : ℕ+ := ⟨k+1, Nat.zero_lt_succ k⟩
    have haa := ha (K • b) (by have h8 := hA K b hb; simp only [inf_eq_inter, sup_le_iff,
      mem_inter_iff, mem_setOf_eq] at h8; exact h8.1.1)
    simp only [natPosSMul_apply, PNat.mk_coe, Nat.cast_add, Nat.cast_one, K] at haa
    have := Complex.norm_log_one_add_half_le_self (z := -cexp (2 * ↑π * Complex.I * (↑k + 1) * b))
    rw [sub_eq_add_neg]
    simp_rw [← mul_assoc] at haa
    rw [haa]
    simp only [forall_exists_index, and_imp, gt_iff_lt, CharP.cast_eq_zero, zero_add, mul_one,
      dist_zero_right, norm_neg, Complex.norm_eq_abs, inf_eq_inter, inter_mem_iff, sup_le_iff,
      mem_inter_iff, mem_setOf_eq, one_div, AbsoluteValue.map_mul, abs_ofNat, Nat.ofNat_pos,
      mul_le_mul_left, ge_iff_le] at *
    apply le_trans (this ?_)
    simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_left]
    have hr := cexp_two_pi_I_im_antimono UpperHalfPlane.I b (n := k + 1) ?_
    simpa using hr
    simp only [UpperHalfPlane.I_im, hb.2.2]
    have HH := ha3 (K • b) (by have h8 := hA K b hb; simp only [inf_eq_inter, sup_le_iff,
      mem_inter_iff, mem_setOf_eq] at h8; exact h8.1.2)
    simp only [natPosSMul_apply, PNat.mk_coe, Nat.cast_add, Nat.cast_one, ← mul_assoc, K] at HH
    exact HH.le
  · intro x n
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
    apply term_ne_zero
  · intro x
    simp only
    have := log_summable_pow (fun n => -cexp (2 * ↑π * Complex.I * (↑n + 1) * x)) ?_ 24
    · apply this.congr
      intro b
      rw [sub_eq_add_neg]
    · rw [←summable_norm_iff]
      simpa using (summable_exp_pow x)

lemma Discriminant_zeroAtImInfty (γ : SL(2, ℤ)): IsZeroAtImInfty
    (Discriminant_SIF ∣[(12 : ℤ)] γ) := by
  rw [IsZeroAtImInfty, ZeroAtFilter]
  have := Discriminant_SIF.slash_action_eq' γ (CongruenceSubgroup.mem_Gamma_one γ)
  simp at *
  rw [this]
  simp [Discriminant_SIF]
  unfold Δ
  rw [show (0 : ℂ) =  0 * 1 by ring]
  apply Tendsto.mul
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [Complex.norm_eq_abs, Complex.abs_exp, mul_re, re_ofNat, ofReal_re, im_ofNat,
      ofReal_im, mul_zero, sub_zero, Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im,
      mul_one, sub_self, coe_re, coe_im, zero_sub, tendsto_exp_comp_nhds_zero,
      tendsto_neg_atBot_iff]
    rw [Filter.tendsto_const_mul_atTop_iff_pos ]
    exact two_pi_pos
    rw [atImInfty]
    exact tendsto_comap
  · apply Delta_boundedfactor

def Delta : CuspForm (CongruenceSubgroup.Gamma 1) 12 where
  toFun := Discriminant_SIF
  slash_action_eq' := Discriminant_SIF.slash_action_eq'
  holo' := by
    rw [mdifferentiable_iff]
    simp
    have := eta_DifferentiableAt_UpperHalfPlane
    have he2 : DifferentiableOn ℂ (fun z => (η z) ^ 24) {z | 0 < z.im} := by
      apply DifferentiableOn.pow
      intro x hx
      apply DifferentiableAt.differentiableWithinAt
      exact this ⟨x, hx⟩
    rw [Discriminant_SIF]
    simp
    apply he2.congr
    intro z hz
    have := Delta_eq_eta_pow (⟨z, hz⟩ : ℍ)
    simp at *
    rw [ofComplex_apply_of_im_pos hz]
    exact this
  zero_at_infty' := fun A => Discriminant_zeroAtImInfty A

lemma Delta_apply (z : ℍ) : Delta z = Δ z := by rfl

lemma Delta_isTheta_rexp : Delta =Θ[atImInfty] (fun τ  => Real.exp (-2 * π * τ.im)) := by
  rw [Asymptotics.IsTheta]
  refine ⟨by simpa using CuspFormClass.exp_decay_atImInfty 1 Delta, ?_⟩
  rw [Asymptotics.isBigO_iff']
  have := Delta_boundedfactor.norm
  simp only [Complex.norm_eq_abs, norm_one] at this
  have h12 : (1 : ℝ) / 2 < 1 :=  one_half_lt_one
  have hl := Filter.Tendsto.eventually_const_le h12 this
  rw [Metric.tendsto_nhds] at *
  use 2
  refine ⟨by simp, ?_⟩
  rw [Filter.eventually_iff_exists_mem] at *
  obtain ⟨A1, hA1, hA2⟩ := hl
  use A1
  refine ⟨hA1, ?_⟩
  intro z hz
  rw [Delta_apply, Δ]
  simp only [neg_mul, Real.norm_eq_abs, Real.abs_exp, norm_mul, Complex.norm_eq_abs]
  have hA3 := hA2 z hz
  conv =>
    enter [2,2,1]
    rw [Complex.abs_exp]
  simp only [mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero, Complex.I_re,
    mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self, coe_re, coe_im, zero_sub]
  have hm : 0 ≤ 2 * rexp (-(2 * π * z.im)) := by
    positivity
  have h4 := mul_le_mul_of_nonneg_left hA3 hm
  conv at h4 =>
    enter [1]
    rw [mul_comm, ← mul_assoc]
    simp
  simp only [gt_iff_lt, one_div, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, ge_iff_le] at *
  rw [← mul_assoc]
  exact h4

lemma CuspForm_apply (k : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma 1) k) (z : ℍ) :
  f.toFun z = f z := by rfl

theorem div_Delta_is_SIF (k : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma 1) k) (γ : SL(2, ℤ)) :
  (⇑f / ⇑Delta) ∣[k - 12] γ = ⇑f / ⇑Delta := by
  ext z
  rw [ModularForm.slash_action_eq'_iff (k -12) _ γ]
  have h0 : (⇑f / ⇑Delta) z = (⇑f z / ⇑Delta z) := rfl
  have h1 : (⇑f / ⇑Delta) (γ • z) = (⇑f (γ • z) / ⇑Delta (γ • z)) := rfl
  have h2 := congrFun (f.slash_action_eq' γ (CongruenceSubgroup.mem_Gamma_one γ)) z
  have h3 := congrFun (Delta.slash_action_eq' γ (CongruenceSubgroup.mem_Gamma_one γ)) z
  rw [ModularForm.slash_action_eq'_iff, CuspForm_apply,  CuspForm_apply] at h2 h3
  rw [h0, h1, h2, h3,  Delta_apply]
  have hD := Δ_ne_zero z
  have := pow_ne_zero  12 (denom_ne_zero γ z)
  rw [ModularGroup.denom_apply] at this
  ring_nf
  nth_rw 2 [mul_comm]
  rw [← inv_zpow, inv_zpow']
  simp_rw [← mul_assoc]
  rw [zpow_add₀ (by apply (denom_ne_zero γ z))]
  ring

def CuspForm_div_Discriminant (k : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma 1) k) :
  ModularForm (CongruenceSubgroup.Gamma 1) (k - 12) where
    toFun := f / Delta
    slash_action_eq' := by
      intro γ _
      apply div_Delta_is_SIF
    holo' := by
      rw [mdifferentiable_iff]
      simp only [SlashInvariantForm.coe_mk]
      have : (⇑f / ⇑Delta) ∘ ↑ofComplex = (⇑f ∘ ↑ofComplex) / (Delta ∘ ↑ofComplex) := by rfl
      rw [this]
      apply DifferentiableOn.div
      · simpa only [CuspForm.toSlashInvariantForm_coe] using
        (UpperHalfPlane.mdifferentiable_iff.mp f.holo')
      · simpa only [CuspForm.toSlashInvariantForm_coe] using
        (UpperHalfPlane.mdifferentiable_iff.mp Delta.holo')
      · intro x hx
        have := Δ_ne_zero ⟨x, hx⟩
        simp only [comp_apply, ne_eq]
        rw [ofComplex_apply_of_im_pos hx]
        apply this
    bdd_at_infty' := by
      intro A
      have h1 := CuspFormClass.exp_decay_atImInfty 1 f
      have h2 := Delta_isTheta_rexp.2
      rw [IsBoundedAtImInfty, BoundedAtFilter] at *
      rw [Asymptotics.isBigO_iff'] at h1 ⊢
      rw [Asymptotics.isBigO_iff''] at h2
      simp only [gt_iff_lt, Complex.norm_eq_abs, neg_mul, Nat.cast_one, div_one, Real.norm_eq_abs,
        Real.abs_exp, SlashInvariantForm.coe_mk, SL_slash, Pi.one_apply, norm_one, mul_one] at *
      obtain ⟨e1, he1, hf⟩ := h1
      obtain ⟨e2, he2, hD⟩ := h2
      use e1/e2
      refine ⟨ by positivity, ?_⟩
      rw [eventually_iff_exists_mem] at *
      obtain ⟨A1, hA, hA2⟩ := hf
      obtain ⟨B2, hB2, hB3⟩ := hD
      use min A1 B2
      refine ⟨by simp [hA, hB2], ?_⟩
      intro z hz
      have : ((⇑f / ⇑Delta) ∣[k - 12] ModularGroup.coe A) z = ((⇑f z / ⇑Delta z)) := by
        have := congrFun (div_Delta_is_SIF k f A) z
        simpa only [SL_slash, Pi.div_apply] using this
      rw [this]
      simp
      have he1e2 : e1 / e2 = (e1 * rexp (-(2 * π * z.im))) / (e2 * rexp (-(2 * π * z.im))) := by
        refine Eq.symm (mul_div_mul_right e1 e2  (Real.exp_ne_zero _))
      rw [he1e2]
      apply div_le_div₀
      · positivity
      · apply hA2
        apply hz.1
      · positivity
      · apply hB3
        apply hz.2

lemma CuspForm_div_Discriminant_apply (k : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma 1) k) (z : ℍ) :
  (CuspForm_div_Discriminant k f) z = f z / Δ z := rfl

theorem CuspForm_div_Discriminant_Add (k : ℤ) (x y : CuspForm (CongruenceSubgroup.Gamma 1) k) :
  (fun f ↦ CuspForm_div_Discriminant k f) (x + y) =
    (fun f ↦ CuspForm_div_Discriminant k f) x + (fun f ↦ CuspForm_div_Discriminant k f) y := by
  ext z
  simp only [CuspForm_div_Discriminant_apply, CuspForm.add_apply, ModularForm.add_apply]
  ring


def Modform_mul_Delta  (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) :
 CuspForm (CongruenceSubgroup.Gamma 1) k where
   toFun := f * Delta
   slash_action_eq' := sorry
   holo' := sorry
   zero_at_infty' := sorry

/-this is done in the modformdims repo, soon to be in mathlib.-/
lemma weigth_zero_rank_eq_one : Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) 0) = 1 :=
  by sorry

/-this is done in the modformdims repo, now in mathlib.-/
lemma neg_weight_rank_zero (k : ℤ) (hk : k < 0) :
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) k) = 0 := by
    exact ModularForm.levelOne_neg_weight_rank_zero hk


def CuspForms_iso_Modforms (k : ℤ) : CuspForm (CongruenceSubgroup.Gamma 1) k ≃ₗ[ℂ]
    ModularForm (CongruenceSubgroup.Gamma 1) (k - 12) where
      toFun f :=  CuspForm_div_Discriminant k f
      map_add' a b := CuspForm_div_Discriminant_Add k a b
      map_smul' := by
        intro m a
        ext z
        simp only [CuspForm_div_Discriminant_apply, CuspForm.smul_apply, smul_eq_mul,
          RingHom.id_apply, ModularForm.smul_apply]
        ring
      invFun f := sorry
      left_inv := sorry
      right_inv := sorry

/-This result is already proven in the modular forms repo and being PRed (slowly) into mathlib, so
we can use it freely here. -/
lemma E_k_q_expansion (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) :
    (E k hk) z = 1 +
        (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) *
        ∑' n : ℕ+, sigma (k - 1) n * Complex.exp (2 * ↑π * Complex.I * z * n) := by sorry

-- lemma E4_E6_q_exp :  ((E₄ z) ^ 3 - (E₆ z) ^ 2) / 1728  =


open SlashInvariantFormClass ModularFormClass
variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} (n : ℕ) (f : F)

open scoped Real MatrixGroups CongruenceSubgroup

lemma IteratedDeriv_smul (a : ℂ)  (f : ℂ → ℂ) (m : ℕ) :
    iteratedDeriv m (a • f) = a • iteratedDeriv m f  := by
  induction' m with m hm
  simp
  rw [iteratedDeriv_succ, iteratedDeriv_succ]
  rw [hm]
  ext x
  rw [@Pi.smul_def]
  exact deriv_const_smul' a (f := iteratedDeriv m f) (x := x)



lemma qExpansion_smul (a : ℂ) (f : CuspForm Γ(n) k) [NeZero n] :
    (a • qExpansion n f) = (qExpansion n (a • f)) := by
  ext m
  simp only [_root_.map_smul, smul_eq_mul]
  simp_rw [qExpansion]
  have : (cuspFunction n (a • f)) = a • cuspFunction n f := by
    ext z
    by_cases h : z = 0
    · rw [h]
      have h0 := CuspFormClass.cuspFunction_apply_zero n (a • f)
      have h1 := CuspFormClass.cuspFunction_apply_zero n f
      simp only [h0, Pi.smul_apply, h1, smul_eq_mul, mul_zero]
    · simp only [cuspFunction, CuspForm.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [Function.Periodic.cuspFunction_eq_of_nonzero _ _ h,
        Function.Periodic.cuspFunction_eq_of_nonzero _ _ h]
      simp only [comp_apply, Pi.smul_apply, smul_eq_mul]
  rw [this]
  simp only [PowerSeries.coeff_mk]
  conv =>
    enter [2,2]
    rw [IteratedDeriv_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring


lemma cuspfunc_Zero [NeZero n] [ModularFormClass F Γ(n) k] : cuspFunction n f 0 = (qExpansion n f).coeff ℂ 0 := by
  have := hasSum_qExpansion_of_abs_lt n f (q := 0) (by simp)
  simp at this
  rw [Summable.hasSum_iff] at this
  sorry
  sorry

local notation "𝕢" => Periodic.qParam




theorem cuspfunc_lim_coef {k : ℤ} {F : Type u_1} [inst : FunLike F ℍ ℂ] (n : ℕ) (c : ℕ → ℂ) (f : F)
  [inst_1 : ModularFormClass F Γ(n) k] [inst_2 : NeZero n] (hf : ∀ (τ : ℍ), HasSum (fun m ↦ c m • 𝕢 ↑n ↑τ ^ m) (f τ))
  (q : ℂ) (hq : ‖q‖ < 1) (hq1 : q ≠ 0) : HasSum (fun m ↦ c m • q ^ m) (cuspFunction n f q) := by
  have hq2 := Function.Periodic.im_invQParam_pos_of_abs_lt_one (h := n)
    (by simp; exact Nat.pos_of_neZero n) hq hq1
  have hft := hf ⟨(Periodic.invQParam (↑n) q), hq2⟩
  have := eq_cuspFunction n f ⟨(Periodic.invQParam (↑n) q), hq2⟩
  simp only [smul_eq_mul, Complex.norm_eq_abs, ne_eq, coe_mk_subtype] at *
  rw [Function.Periodic.qParam_right_inv] at this hft
  rw [← this] at hft
  exact hft
  · simp only [ne_eq, Nat.cast_eq_zero]
    exact NeZero.ne n
  · exact hq1
  · simp only [ne_eq, Nat.cast_eq_zero]
    exact NeZero.ne n
  · exact hq1


lemma tsum_zero_pow (f : ℕ → ℂ) : (∑' m, f m * 0 ^ m) = f 0 := by
  rw [tsum_eq_zero_add]
  simp only [pow_zero, mul_one, ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false,
    not_false_eq_true, zero_pow, mul_zero, tsum_zero, add_zero]
  rw [← summable_nat_add_iff 1]
  simp only [ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
    zero_pow, mul_zero]
  apply summable_zero

lemma modfom_q_exp_cuspfunc  (c : ℕ → ℂ) (f : F) [ModularFormClass F Γ(n) k]
    [NeZero n]
    (hf : ∀ τ : ℍ,  HasSum (fun m : ℕ ↦ (c m) • 𝕢 n τ ^ m) (f τ)) : ∀ q : ℂ, ‖q‖ < 1 →
    HasSum (fun m : ℕ ↦ c m • q ^ m) (cuspFunction n f q) := by
  intro q hq
  by_cases hq1 : q ≠ 0
  ·  apply cuspfunc_lim_coef n c f hf q hq hq1
  · --have h1 : Tendsto (fun z : ℍ => ∑' i, c i * (𝕢 n z) ^ n) atImInfty (𝓝 (c 0)) := by sorry
    have h2 : cuspFunction n f 0 = c 0 := by
      rw [cuspFunction, Function.Periodic.cuspFunction_zero_eq_limUnder_nhds_ne]
      apply Filter.Tendsto.limUnder_eq
      have := cuspfunc_lim_coef n c f hf
      rw [cuspFunction] at this
      have htt : Tendsto (fun q => ∑' m, c m * q ^ m) (𝓝[≠] 0) (𝓝 (c 0)) := by
        have hD := tendsto_tsum_of_dominated_convergence (𝓕 := (𝓝[≠] (0 : ℂ)))
          (f := fun q : ℂ => fun m : ℕ => c m * q ^ m) (g := fun m : ℕ => c m * 0 ^ m) (bound := fun m => ‖c m‖ * (1 / 2 ) ^ m ) ?_ ?_ ?_
        convert hD
        simp only
        rw [tsum_zero_pow]
        have ht3 := (this (1/2) (by norm_num) (by apply one_div_ne_zero; exact Ne.symm (NeZero.ne' 2))).summable.norm
        simpa using ht3
        intro k
        apply Tendsto.const_mul
        have := ((continuous_pow k (M := ℂ) ).tendsto) 0
        apply Filter.Tendsto.mono_left this
        exact nhdsWithin_le_nhds
        rw [eventually_iff_exists_mem]
        use {z | (z : ℂ) ≠ 0 ∧ ‖z‖ < 1 / 2}
        constructor
        · rw [@mem_nhdsWithin_iff]
          refine ⟨1/2, by norm_num, ?_⟩
          intro y hy
          simp only [smul_eq_mul, Complex.norm_eq_abs, ne_eq, Decidable.not_not, one_div,
            mem_inter_iff, mem_ball, dist_zero_right, mem_compl_iff, mem_singleton_iff,
            mem_setOf_eq] at *
          refine ⟨hy.2, hy.1⟩
        · intro y hy k
          simp only [norm_mul, Complex.norm_eq_abs, norm_pow, one_div, inv_pow]
          gcongr
          have hy2 := hy.2.le
          rw [← inv_pow]
          gcongr
          simpa only [Complex.norm_eq_abs, one_div] using hy2
      apply htt.congr'
      rw [@eventuallyEq_nhdsWithin_iff, eventually_nhds_iff_ball]
      use 1
      simp only [gt_iff_lt, zero_lt_one, mem_ball, dist_zero_right, Complex.norm_eq_abs,
        mem_compl_iff, mem_singleton_iff, true_and]
      intro y hy hy0
      exact (this y hy hy0).tsum_eq
    simp only [ne_eq, Decidable.not_not] at hq1
    simp_rw [hq1]
    rw [h2]
    simp only [smul_eq_mul]
    rw [Summable.hasSum_iff]
    apply tsum_zero_pow
    rw [← summable_nat_add_iff 1]
    simp only [ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
    zero_pow, mul_zero]
    apply summable_zero

lemma q_exp_unique (c : ℕ → ℂ) (f : ModularForm Γ(n) k) [NeZero n]
    (hf : ∀ τ : ℍ,  HasSum (fun m : ℕ ↦ (c m) • 𝕢 n τ ^ m) (f τ))  :
    c = (fun m => (qExpansion n f).coeff ℂ m) := by
  ext m
  have h := hasFPowerSeries_cuspFunction n f
  let qExpansion2 : PowerSeries ℂ := .mk fun m ↦ c m
  let qq : FormalMultilinearSeries ℂ ℂ ℂ :=
    fun m ↦ (qExpansion2).coeff ℂ m • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m _
  have hqq2 :  ∀ m , ‖qq m‖ = ‖(qExpansion2).coeff ℂ m‖ := by
    intro m
    simp only [qq]
    rw [
    ← (ContinuousMultilinearMap.piFieldEquiv ℂ (Fin m) ℂ).symm.norm_map]
    simp only [_root_.map_smul, smul_eq_mul, norm_mul, Complex.norm_eq_abs,
      LinearIsometryEquiv.norm_map, ContinuousMultilinearMap.norm_mkPiAlgebraFin, mul_one]
  have H2 : HasFPowerSeriesOnBall (cuspFunction n f) qq 0 1 := by
    have H21 : 1 ≤ qq.radius := by
        refine le_of_forall_ge_of_dense fun r hr ↦ ?_
        lift r to NNReal using hr.ne_top
        apply FormalMultilinearSeries.le_radius_of_summable
        conv =>
          enter [1]
          intro n
          rw [hqq2]
        simp only [PowerSeries.coeff_mk, Complex.norm_eq_abs, qExpansion2, qq]
        sorry
    refine ⟨H21 , zero_lt_one, ?_⟩
    intro y hy
    rw [EMetric.mem_ball, edist_zero_right, ENNReal.coe_lt_one_iff, ← NNReal.coe_lt_one,
    coe_nnnorm, Complex.norm_eq_abs] at hy
    simp
    have := modfom_q_exp_cuspfunc n c f hf y hy
    apply this.congr
    intro S
    congr
    ext b
    simp only [smul_eq_mul, PowerSeries.coeff_mk, qq, qExpansion2]
    rw [mul_comm]
    congr
    rw [FormalMultilinearSeries.coeff.eq_1 ]
    simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
      smul_eq_mul, qExpansion2, qq]
    rw [@Fin.prod_ofFn]
    simp only [Pi.one_apply, Finset.prod_const_one, mul_one, qExpansion2, qq]
  have h3 : HasFPowerSeriesAt (cuspFunction n f) qq 0 := by
    rw [HasFPowerSeriesAt]
    use 1
  have h4 : HasFPowerSeriesAt (cuspFunction n f) (qExpansionFormalMultilinearSeries n f) 0 := by
    rw [HasFPowerSeriesAt]
    use 1
  have := HasFPowerSeriesAt.eq_formalMultilinearSeries h3 h4
  rw [@FormalMultilinearSeries.ext_iff] at this
  have h5 := this m
  simp only [PowerSeries.coeff_mk, qExpansionFormalMultilinearSeries, qq, qExpansion2] at h5
  let t := c m • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m ℂ m
  let v :=   (PowerSeries.coeff ℂ m) (qExpansion n f) • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m ℂ m
  have htv : (c m • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m ℂ).toFun =
    ( (PowerSeries.coeff ℂ m) (qExpansion n f) • ContinuousMultilinearMap.mkPiAlgebraFin ℂ m ℂ).toFun := by
    rw [h5]
  have h6 := congrFun htv m
  simpa only [ContinuousMultilinearMap.toMultilinearMap_smul, Pi.natCast_def,
    MultilinearMap.toFun_eq_coe, MultilinearMap.smul_apply, ContinuousMultilinearMap.coe_coe,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.ofFn_const, List.prod_replicate,
    smul_eq_mul, mul_eq_mul_right_iff, pow_eq_zero_iff', Nat.cast_eq_zero, ne_eq, and_not_self,
    or_false, qExpansion2, qq] using h6


theorem modform_tendto_ndhs_zero {k : ℤ} (n : ℕ) (f : ModularForm Γ(n) k) [inst : NeZero n] :
    Tendsto (fun x ↦ (⇑f ∘ ↑ofComplex) (Periodic.invQParam (↑n) x)) (𝓝[≠] 0)
    (𝓝 (cuspFunction n f 0)) := by
  simp only [comp_apply]
  have h1 := Function.Periodic.boundedAtFilter_cuspFunction (h := n)
    (by simp only [Nat.cast_pos]; exact Nat.pos_of_neZero n)
    (bounded_at_infty_comp_ofComplex f)
  have h2 : Tendsto (cuspFunction n f) (𝓝[≠] 0) (𝓝 (cuspFunction n f 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    apply (Function.Periodic.differentiableAt_cuspFunction_zero (h := n)
      (by simp only [Nat.cast_pos]; exact Nat.pos_of_neZero n) ?_ ?_ ?_).continuousAt.tendsto
    apply SlashInvariantFormClass.periodic_comp_ofComplex
    simp only [eventually_comap, eventually_atTop, ge_iff_le]
    use 1
    intro b hb a ha
    apply ModularFormClass.differentiableAt_comp_ofComplex (z := a)
    rw [ha]
    linarith
    apply ModularFormClass.bounded_at_infty_comp_ofComplex
  apply h2.congr'
  rw [@eventuallyEq_nhdsWithin_iff, eventually_iff_exists_mem]
  use ball 0 1
  constructor
  apply Metric.ball_mem_nhds
  exact Real.zero_lt_one
  intro y hy hy0
  apply Function.Periodic.cuspFunction_eq_of_nonzero
  simpa only [ne_eq, mem_compl_iff, mem_singleton_iff] using hy0

theorem cuspFunction_mul_zero (n : ℕ) (a b : ℤ) (f : ModularForm Γ(n) a) (g : ModularForm Γ(n) b) [inst : NeZero n] :
    cuspFunction n (f.mul g) 0 = cuspFunction n f 0 * cuspFunction n g 0 := by
  rw [cuspFunction, Periodic.cuspFunction ]
  simp only [mul_coe, update_self]
  apply Filter.Tendsto.limUnder_eq
  have : (⇑f * ⇑g) ∘ ↑ofComplex = (⇑f ∘ ↑ofComplex) * (⇑g ∘ ↑ofComplex) := by
    ext y
    simp only [comp_apply, Pi.mul_apply]
  rw [this]
  apply Filter.Tendsto.mul
  · apply modform_tendto_ndhs_zero
  · apply modform_tendto_ndhs_zero


lemma qExpansion_mul_coeff_zero (a b : ℤ) (f : ModularForm Γ(n) a) (g : ModularForm Γ(n) b)
    [NeZero n] : (qExpansion n (f.mul g)).coeff ℂ 0 =
      (((qExpansion n f)).coeff ℂ 0) * ((qExpansion n g)).coeff ℂ 0 := by
    simp_rw [qExpansion_coeff ]
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, iteratedDeriv_zero, one_mul]
    apply cuspFunction_mul_zero

lemma cuspFunction_mul (a b : ℤ) (f : ModularForm Γ(n) a) (g : ModularForm Γ(n) b)
    [NeZero n] : cuspFunction n (f.mul g) = cuspFunction n f * cuspFunction n g := by
    ext z
    by_cases h : z = 0
    rw [h]
    simp only [Pi.mul_apply]
    apply cuspFunction_mul_zero
    simp_rw [cuspFunction, Periodic.cuspFunction]
    simp only [mul_coe, ne_eq, h, not_false_eq_true, update_of_ne, comp_apply, Pi.mul_apply]

/- lemma IteratedDeriv_mul_eq (f g : ℂ → ℂ)  (m : ℕ) :
    iteratedDeriv m (f * g) = ∑ i ∈ Finset.antidiagonal m, ((f * iteratedDeriv i.1 g) +
      g * (iteratedDeriv i.2 f)) := by
  induction' m with m hm
  simp only [iteratedDeriv_zero, Finset.antidiagonal_zero, Prod.mk_zero_zero, Finset.sum_singleton,
    Prod.fst_zero, Prod.snd_zero, self_eq_add_right]
  rw [iteratedDeriv_succ, iteratedDeriv_succ, hm]
  simp only [mul_add, add_mul, sum_range_succ, mul_assoc, mul_comm, mul_left_comm]
 -/

lemma deriv_mul_eq (f g : ℂ → ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    deriv (f * g) = deriv f *  g + f * deriv g := by
  ext y
  exact deriv_mul (hf y) (hg y)

lemma IteratedDeriv_mul (f g : ℂ → ℂ) (m : ℕ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    iteratedDeriv m (f * g) =
    ∑ i in Finset.range m.succ, (m.choose i) * (iteratedDeriv i f) * (iteratedDeriv (m - i) g) := by
  induction' m with m hm generalizing f g
  simp only [iteratedDeriv_zero, Finset.sum_singleton, Finset.range_one, Finset.mem_singleton,
    Nat.choose_zero_right, Nat.sub_zero, Nat.choose_one_right, Nat.sub_self, mul_one]
  ring
  --rw [iteratedDeriv_succ', deriv_mul_eq f g hf hg]
  rw [iteratedDeriv_succ, hm]
  ext y
  simp
  have := deriv_sum (A := fun i => (((m.choose i) : ℂ) • (iteratedDeriv i f) * (iteratedDeriv (m - i) g ))) (u := Finset.range (m+1)) (x := y) ?_
  simp at *
  have hy : (fun y ↦ ∑ x ∈ Finset.range (m + 1), ↑(m.choose x) * iteratedDeriv x f y * iteratedDeriv (m - x) g y) =
    (∑ x ∈ Finset.range (m + 1), (fun y => ↑(m.choose x) * iteratedDeriv x f * iteratedDeriv (m - x) g) y) := by
    exact
      Eq.symm
        (Finset.sum_fn (Finset.range (m + 1)) fun c y ↦
          ↑(m.choose c) * iteratedDeriv c f y * iteratedDeriv (m - c) g y)
  rw [hy] at this

  conv =>
    enter [1]
    --rw [this]
  sorry
  sorry
  sorry
  sorry


lemma qExpansion_mul_coeff (a b : ℤ) (f : ModularForm Γ(n) a) (g : ModularForm Γ(n) b)
    [NeZero n] : (qExpansion n (f.mul g)) = ((qExpansion n f)) * ((qExpansion n g)) := by
  ext m
  induction' m with m hm
  simpa using qExpansion_mul_coeff_zero n a b f g
  rw [PowerSeries.coeff_mul ] at *
  --have := PowerSeries.coeff_succ_mul_X
  simp_rw [qExpansion_coeff, cuspFunction_mul ] at *
  rw [iteratedDeriv_succ']
  --have := FormalMultilinearSeries.coeff_fslope
  --have := deriv_mul (c:= cuspFunction n f) (d := cuspFunction n g)
 /-  by_cases h : m = 0
  simp_rw [h]
  simpa using qExpansion_mul_coeff_zero n a b f g
  rw [PowerSeries.coeff_mul ]
  simp_rw [qExpansion_coeff ] -/

  sorry


/-


lemma cuspform_iff_coeff_zero (f : ModularForm Γ(n) k) [NeZero n] (A : SL(2, ℤ)) :
    (qExpansion n f).coeff ℂ 0 = 0 ↔  f.1.1 ∈ CuspForm Γ(n) k := by
  split
  · intro h
    have h1 := Function.Periodic.cuspFunction_eq_of_nonzero (h := n)
      (by simp only [Nat.cast_pos]; exact Nat.pos_of_neZero n) h
    rw [cuspFunction, Periodic.cuspFunction] at h1
    simp only [update_self, mul_coe] at h1
    exact h1
  · intro h
    have h1 := Function.Periodic.cuspFunction_eq_of_nonzero (h := n)
      (by simp only [Nat.cast_pos]; exact Nat.pos_of_neZero n) h
    rw [cuspFunction, Periodic.cuspFunction] at h1
    simp only [update_self, mul_coe] at h1
    exact h1 -/



def ModForm_mk (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : CuspForm Γ k ) : ModularForm Γ k where
  toFun := f
  slash_action_eq' := f.slash_action_eq'
  holo' := f.holo'
  bdd_at_infty' A := (f.zero_at_infty' A).boundedAtFilter

def CuspForm_to_ModularForm (Γ : Subgroup SL(2, ℤ)) (k : ℤ) : CuspForm Γ k →ₗ[ℂ] ModularForm Γ k where
  toFun f := ModForm_mk Γ k f
  map_add' := by
    intro f g
    simp only [ModForm_mk, CuspForm.coe_add]
    rfl
  map_smul' := by
    intro m f
    simp only [ModForm_mk, CuspForm.coe_smul, RingHom.id_apply]
    rfl

def CuspFormSubmodule (Γ : Subgroup SL(2, ℤ)) (k : ℤ)  : Submodule ℂ (ModularForm Γ k) :=
  LinearMap.range (CuspForm_to_ModularForm Γ k)

def IsCuspForm (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k) : Prop :=
  f ∈ CuspFormSubmodule Γ k

def IsCuspForm_to_CuspForm (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k)
    (hf : IsCuspForm Γ k f) : CuspForm Γ k := by
  rw [IsCuspForm, CuspFormSubmodule, LinearMap.mem_range] at hf
  exact hf.choose

lemma CuspForm_to_ModularForm_coe (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k)
    (hf : IsCuspForm Γ k f) : (IsCuspForm_to_CuspForm Γ k f hf).toSlashInvariantForm =
    f.toSlashInvariantForm := by
  rw [IsCuspForm_to_CuspForm]
  rw [IsCuspForm, CuspFormSubmodule, LinearMap.mem_range] at hf
  have hg := hf.choose_spec
  simp_rw [CuspForm_to_ModularForm] at hg
  have hgg := congr_arg (fun x ↦ x.toSlashInvariantForm) hg
  simp [ModForm_mk] at *
  exact hgg

instance : FunLike (ℍ → ℂ) ℍ ℂ where
  coe f := f
  coe_injective' := fun ⦃_ _⦄ a ↦ a

lemma IsCuspForm_iff_coeffZero_eq_zero  (k : ℤ) (f : ModularForm Γ(1) k) :
    IsCuspForm Γ(1) k f ↔ (qExpansion 1 f).coeff ℂ 0 = 0 := by
  constructor
  · intro h
    rw [qExpansion_coeff]
    simp
    rw [IsCuspForm, CuspFormSubmodule, LinearMap.mem_range] at h
    obtain ⟨g, hg⟩ := h
    have := CuspFormClass.cuspFunction_apply_zero 1 g
    simp [CuspForm_to_ModularForm, ModForm_mk] at hg
    rw [← hg]
    exact this
  · intro h
    rw [IsCuspForm]
    rw [CuspFormSubmodule, LinearMap.mem_range]
    use ⟨f.toSlashInvariantForm , f.holo', ?_⟩
    · simp only [CuspForm_to_ModularForm, ModForm_mk]
      rfl
    · intro A
      have hf := f.slash_action_eq' A (CongruenceSubgroup.mem_Gamma_one A)
      simp only [ SlashInvariantForm.toFun_eq_coe, toSlashInvariantForm_coe, SL_slash] at *
      rw [hf]
      rw [qExpansion_coeff] at h
      simp only [Nat.factorial_zero, Nat.cast_one, inv_one, iteratedDeriv_zero, one_mul] at h
      have := modform_tendto_ndhs_zero 1 f
      rw [h] at this
      have hgg : (fun x ↦ (⇑f ∘ ↑ofComplex) (Periodic.invQParam (1 : ℕ) x)) = ((⇑f ∘ ↑ofComplex) ∘ (Periodic.invQParam (1 : ℕ))) := by
        rfl
      rw [hgg] at this
      have hgg2 := this.comp (Function.Periodic.qParam_tendsto (h := 1) ( Real.zero_lt_one))
      have hgg3 := hgg2.comp tendsto_coe_atImInfty
      rw [IsZeroAtImInfty, ZeroAtFilter]
      apply hgg3.congr'
      rw [Filter.eventuallyEq_iff_exists_mem]
      use ⊤
      simp only [top_eq_univ, univ_mem, Nat.cast_one, eqOn_univ, true_and]
      ext y
      simp only [comp_apply]
      have h5 := periodic_comp_ofComplex 1 f
      have := Function.Periodic.qParam_left_inv_mod_period (h := 1) (Ne.symm (zero_ne_one' ℝ)) y
      obtain ⟨m, hm⟩ := this
      have h6 := Function.Periodic.int_mul h5 m y
      simp only [Nat.cast_one, comp_apply, Periodic, ofReal_one, mul_one, ofComplex_apply] at *
      rw [← hm] at h6
      exact h6

def foo : ModularForm Γ(1) 12 := (E₄).mul ((E₄).mul E₄)

def bar : ModularForm Γ(1) 12 := (E₆).mul E₆

def foobar : ModularForm Γ(1) 12 :=(1/ 1728 : ℂ) • (foo - bar)

lemma auxasdf (n : ℕ) : (PowerSeries.coeff ℂ n) ((qExpansion 1 E₄) * (qExpansion 1 E₆)) =
    ∑ p ∈ Finset.antidiagonal n, (PowerSeries.coeff ℂ p.1) ((qExpansion 1 E₄)) * (PowerSeries.coeff ℂ p.2) ((qExpansion 1 E₆)) := by
  apply PowerSeries.coeff_mul



def Delta_E4_E6_aux : CuspForm (CongruenceSubgroup.Gamma 1) 12 := by sorry




lemma delta_eq_E4E6_const : ∃ (c : ℂ), c ≠ 0 ∧ (c • Delta) = Delta_E4_E6_aux := by sorry

lemma Delta_q_one_term : (qExpansion 1 Delta).coeff ℂ 1 = 1 := by
  rw [qExpansion_coeff]
  simp
  apply HasDerivAt.deriv
  refine hasDerivAt_iff_tendsto_slope_zero.mpr ?_
  rw [CuspFormClass.cuspFunction_apply_zero 1 Delta]
  simp
  have HT : Tendsto (fun z => z⁻¹ * (Delta ∘ ofComplex) ((Periodic.invQParam 1 z))) (𝓝[≠] 0) (𝓝 1) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    rw [eventually_iff_exists_mem]
    use {z | (z : ℂ) ≠ 0 ∧ ‖z‖ < 1}
    constructor
    ·
      rw [@mem_nhdsWithin_iff]
      use 1
      simp
      intro y hy
      simp at hy
      aesop
    · intro y hy
      simp
      have hz :=Function.Periodic.im_invQParam_pos_of_abs_lt_one (h := 1) (by exact Real.zero_lt_one) hy.2 hy.1
      have :=  ofComplex_apply_of_im_pos hz
      rw [this, Delta_apply]



      --ofComplex_apply_of_im_pos
      sorry




  apply Filter.Tendsto.congr' _ HT


  sorry



lemma Delta_E4_E6_aux_q_one_term : (qExpansion 1 Delta_E4_E6_aux).coeff ℂ 1 = 1 := by sorry

theorem Delta_E4_eqn (z : UpperHalfPlane) : Delta = Delta_E4_E6_aux  := by
  ext z
  obtain ⟨c, hc, H⟩ := delta_eq_E4E6_const
  suffices h2 : c  = 1 by
    simp [Delta, Discriminant_SIF]
    sorry
/-     rw [h2]
    simp
    rfl -/
  · have Qe4 := E_k_q_expansion 4 (by norm_num) (sorry) z
    have Qe6 := E_k_q_expansion 6 (by norm_num) (sorry) z
    /- rw [E4_apply, E6_apply] at h
    zify at *
    rw [Qe4, Qe6] at h -/
    have h1 := Delta_q_one_term
    have h2 := Delta_E4_E6_aux_q_one_term
    sorry
    /- rw [← h] at h2
    have := qExpansion_smul 1 c Delta
    rw [← this] at h2
    simp at h2
    rw [h1] at h2
    simpa using h2 -/
--enough to check its a cuspform, since if it is, then divining by Δ gives a modular form of weight 0.

lemma weight_two_zero (f : ModularForm (CongruenceSubgroup.Gamma 1) 2) : f = 0 := sorry
/- cant be a cuspform from the above, so let a be its constant term, then f^2 = a^2 E₄ and
f^3 = a^3 E₆, but now this would mean that Δ = 0 or a = 0, which is a contradiction. -/

lemma dim_modforms_eq_one_add_dim_cuspforms (k : ℤ) (hk : 2 < k):
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) k) =
    1 + Module.rank ℂ (CuspForm (CongruenceSubgroup.Gamma 1) k) := sorry

lemma dim_modforms_lvl_one (k : ℤ) :
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) k) = if 12 ∣ k - 2 then
    Nat.floor (k / 12) else Nat.floor (k / 12) + 1 := sorry

lemma dim_gen_cong_levels (k : ℤ) (Γ : Subgroup SL(2, ℤ)) (hΓ : Subgroup.index Γ ≠ 0) :
    FiniteDimensional ℂ (ModularForm Γ k) := by sorry
--use the norm to turn it into a level one question.


end Product_Formula

open ArithmeticFunction

section Ramanujan_Formula

-- In this section, we state some simplifications that are used in Cor 7.5-7.7 of the blueprint

theorem E₂_mul_E₄_sub_E₆ (z : ℍ) :
    (E₂ z) * (E₄ z) - (E₆ z) = 720 * ∑' (n : ℕ+), n * (σ 3 n) * cexp (2 * π * Complex.I * n * z) := by
  sorry

end Ramanujan_Formula

#min_imports
