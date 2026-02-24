module
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls


/-!
# Volume of balls

This file proves results such as `EuclideanSpace.volume_ball_pos` and
`EuclideanSpace.volume_ball_lt_top`.
-/

open Metric MeasureTheory

variable {r : ℝ} {ι : Type*} [Fintype ι]

/-- The Lebesgue volume of a nontrivial Euclidean ball is positive. -/
public theorem EuclideanSpace.volume_ball_pos [Nonempty ι] (x : EuclideanSpace ℝ ι) (hr : 0 < r) :
    0 < volume (ball x r) := by
  simpa using measure_ball_pos (μ := volume) x hr


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
  congr 1
  ext t
  exact False.elim (IsEmpty.false t)

/-- The Lebesgue volume of a Euclidean ball is finite. -/
public theorem EuclideanSpace.volume_ball_lt_top
    [NoAtoms (volume : Measure (EuclideanSpace ℝ ι))] (x : EuclideanSpace ℝ ι) :
    volume (ball x r) < ⊤ := by
  simpa using measure_ball_lt_top (μ := volume) (x := x) (r := r)
