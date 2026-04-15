module
public import Mathlib.Topology.Instances.Complex
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Tendsto Lemmas

This file collects small helper lemmas about `Filter.Tendsto` along `atTop`, mostly for
changing index types and combining limits.

## Main statements
* `int_tendsto_nat`
* `pnat_tendsto_nat`, `nat_tendsto_pnat`
* `tendsto_of_tendsto_sub`
* `tendsto_one_sub_pow_atTop`
-/

open scoped Topology

open Filter TopologicalSpace

/-- If `f : ℤ → ℂ` tends to `x` at `atTop`, then `fun n : ℕ => f n` tends to `x` at `atTop`. -/
public lemma int_tendsto_nat {f : ℤ → ℂ} {x : ℂ} (hf : Tendsto f atTop (𝓝 x)) :
    Tendsto (fun n : ℕ => f n) atTop (𝓝 x) :=
  hf.comp tendsto_natCast_atTop_atTop

/-- If `fun n : ℕ+ => f n` tends to `x`, then `f` tends to `x` (viewing `ℕ+` as cofinal in `ℕ`). -/
public lemma pnat_tendsto_nat {α : Type*} [TopologicalSpace α] (f : ℕ → α) (x : α)
    (hf : Tendsto (fun n : ℕ+ => f n) atTop (𝓝 x)) :
    Tendsto f atTop (𝓝 x) :=
  tendsto_comp_val_Ioi_atTop.mp hf

/-- If `f` tends to `x`, then so does `fun n : ℕ+ => f n`. -/
public lemma nat_tendsto_pnat {α : Type*} [TopologicalSpace α] (f : ℕ → α) (x : α)
    (hf : Tendsto f atTop (𝓝 x)) :
    Tendsto (fun n : ℕ+ => f n) atTop (𝓝 x) :=
  tendsto_comp_val_Ioi_atTop.mpr hf

/-- If `f → x` and `g - f → 0`, then `g → x`. -/
public lemma tendsto_of_tendsto_sub (f g : ℕ → ℂ) (x : ℂ) (hf : Tendsto f atTop (𝓝 x))
    (hfg : Tendsto (g - f) atTop (𝓝 0)) : Tendsto g atTop (𝓝 x) := by
  simpa [sub_eq_add_neg, add_assoc] using hf.add hfg

lemma aux47 (r : ℂ) (hr : ‖r‖ < 1) : Tendsto (fun n : ℕ => 1 - r^n) atTop (𝓝 1) := by
  simpa using tendsto_const_nhds.sub <| tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr
