module
public import SpherePacking.Basic.SpherePacking
public import SpherePacking.E8.Packing
import SpherePacking.CohnElkies.LPBound
import SpherePacking.MagicFunction.g.CohnElkies.ScaledMagic

/-!
# Upper bound for sphere packing in dimension 8

Proves an upper bound for `SpherePackingConstant 8` using the Cohn-Elkies linear programming
bound and Viazovska's magic function (after a scaling), and packages the final main theorem.

## Main statements
* `SpherePacking.SpherePackingConstant_le_E8Packing_density`
* `SpherePacking.MainTheorem`
-/

namespace SpherePacking

open scoped FourierTransform ENNReal SchwartzMap
open MeasureTheory Real SpherePacking Metric

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

/-- Upper bound on `SpherePackingConstant 8` given by the density of the `E8` lattice packing. -/
public theorem SpherePackingConstant_le_E8Packing_density :
    SpherePackingConstant 8 ≤ E8Packing.density := by
  have hne : (scaledMagic : 𝓢(ℝ⁸, ℂ)) ≠ 0 := fun h => by
    simpa [scaledMagic_zero] using congrArg (fun f : 𝓢(ℝ⁸, ℂ) => f 0) h
  have hLP :
      SpherePackingConstant 8 ≤ (scaledMagic 0).re.toNNReal / (𝓕 (⇑scaledMagic) 0).re.toNNReal *
        volume (ball (0 : ℝ⁸) (1 / 2 : ℝ)) := by
    simpa using
      (LinearProgrammingBound (d := 8) (f := (scaledMagic : 𝓢(ℝ⁸, ℂ))) hne
        scaledMagic_real' scaledMagic_real_fourier' scaledMagic_cohnElkies₁'
        scaledMagic_cohnElkies₂' (Nat.succ_pos 7))
  have hratio : (scaledMagic 0).re.toNNReal / (𝓕 (⇑scaledMagic) 0).re.toNNReal = (16 : ℝ≥0∞) := by
    simp [ENNReal.ofNNReal_toNNReal, scaledMagic_zero, fourier_scaledMagic_zero_fun]
  calc
    SpherePackingConstant 8 ≤ (16 : ℝ≥0∞) * volume (ball (0 : ℝ⁸) (1 / 2 : ℝ)) := by
      simpa [mul_assoc, hratio] using hLP
    _ = ENNReal.ofReal π ^ 4 / 384 := by
      calc (16 : ℝ≥0∞) * volume (ball (0 : ℝ⁸) (1 / 2 : ℝ))
          = (16 : ℝ≥0∞) *
            (ENNReal.ofReal (1 / 2 : ℝ) ^ 8 * ENNReal.ofReal (π ^ 4 / 24)) := by
            simp [InnerProductSpace.volume_ball_of_dim_even (E := ℝ⁸) (k := 4) (hk := by simp),
              finrank_euclideanSpace, Nat.factorial]
        _ = ENNReal.ofReal ((16 : ℝ) * (((1 / 2 : ℝ) ^ 8) * (π ^ 4 / 24))) := by
            have hinv : (2⁻¹ : ℝ≥0∞) ^ 8 = (2 ^ 8 : ℝ≥0∞)⁻¹ := by
              simpa using (ENNReal.inv_pow (a := (2 : ℝ≥0∞)) (n := 8)).symm
            simp [mul_left_comm, ENNReal.ofReal_mul, (by norm_num : (0 : ℝ) ≤ (16 : ℝ)), hinv]
        _ = ENNReal.ofReal (π ^ 4 / 384 : ℝ) := by congr 1; ring
        _ = ENNReal.ofReal π ^ 4 / 384 := by
            simp [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 384),
              ENNReal.ofReal_pow Real.pi_pos.le]
    _ = E8Packing.density := by simpa using E8Packing_density.symm

open SpherePacking E8

/-- Main theorem (dimension 8): the optimal packing density equals `E8Packing.density`. -/
public theorem MainTheorem : SpherePackingConstant 8 = E8Packing.density :=
  le_antisymm SpherePackingConstant_le_E8Packing_density <| by
    simpa [SpherePackingConstant] using
      le_iSup (fun S : SpherePacking 8 => S.density) E8Packing.toSpherePacking

end SpherePacking
