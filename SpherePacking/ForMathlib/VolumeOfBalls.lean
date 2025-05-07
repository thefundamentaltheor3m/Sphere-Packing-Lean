import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/- This file contains several (semi-adhoc) lemmas about volume of balls, e.g. that they are positive
generally, or 0 over (ι → ℝ) if ι is Empty. -/

open Metric MeasureTheory MeasureSpace ENNReal

variable {r : ℝ} {ι : Type*} [Fintype ι]

theorem EuclideanSpace.volume_ball_pos [Nonempty ι] (x : EuclideanSpace ℝ ι) (hr : 0 < r) :
    0 < volume (ball x r) := by
  rw [volume_ball]
  apply ENNReal.mul_pos
  · exact pow_ne_zero _ <| ENNReal.ofReal_eq_zero.not.mpr <| not_le_of_gt hr
  · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    apply div_pos
    · exact pow_pos (Real.sqrt_pos.mpr Real.pi_pos) _
    · apply Real.Gamma_pos_of_pos
      have : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
      linarith

open Classical in
noncomputable def Fintype.ofSingletonOnly (α : Type*) [Subsingleton α] : Fintype α :=
  if h : Nonempty α then
    Fintype.ofSubsingleton (Classical.choice h)
  else
    @Fintype.ofIsEmpty _ (not_nonempty_iff.mp h)

theorem MeasureTheory.MeasureSpace.volume_subsingleton
    {α : Type*} [MeasureSpace α] {s : Set α} (hs : Subsingleton s) [NoAtoms (volume : Measure α)] :
      volume s = 0 := by
  obtain ⟨s', hs'⟩ := Fintype.ofSingletonOnly s
  convert Finset.measure_zero (s'.map ⟨Subtype.val, Subtype.val_injective⟩) volume
  ext x
  simp [hs']

theorem EuclideanSpace.ball_subsingleton [IsEmpty ι]
    (x : EuclideanSpace ℝ ι) : Subsingleton (ball x r) := by
  apply Subsingleton.intro
  intro ⟨x, _⟩ ⟨y, _⟩
  change ι → ℝ at x y
  ext t
  exact False.elim (IsEmpty.false t)

theorem EuclideanSpace.volume_ball_lt_top [inst : NoAtoms (volume : Measure (EuclideanSpace ℝ ι))]
    (x : EuclideanSpace ℝ ι) : volume (ball x r) < ⊤ := by
  by_cases h : Nonempty ι
  · rw [volume_ball]
    exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
  · rw [volume_subsingleton <| @EuclideanSpace.ball_subsingleton _ _ _ (not_nonempty_iff.mp h) _]
    exact zero_lt_top
