module
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls


/-!
# Volume of balls

This file proves results such as `EuclideanSpace.volume_ball_pos` and
`EuclideanSpace.volume_ball_lt_top`.
-/

open Metric MeasureTheory

variable {r : ℝ} {ι : Type*} [Fintype ι]

theorem EuclideanSpace.volume_ball_pos [Nonempty ι] (x : EuclideanSpace ℝ ι) (hr : 0 < r) :
    0 < volume (ball x r) :=
  -- `volume` on `EuclideanSpace` is an `IsOpenPosMeasure`, so this is mathlib's
  -- `Metric.measure_ball_pos`.
  Metric.measure_ball_pos volume x hr

open Classical in
@[implicit_reducible]
noncomputable def Fintype.ofSingletonOnly (α : Type*) [Subsingleton α] : Fintype α :=
  if h : Nonempty α then
    Fintype.ofSubsingleton (Classical.choice h)
  else
    @Fintype.ofIsEmpty _ (not_nonempty_iff.mp h)

-- `volume_subsingleton` is now mathlib's `Set.Subsingleton.measure_zero`
-- (`((Set.subsingleton_coe s).mp hs).measure_zero volume`).

theorem EuclideanSpace.ball_subsingleton [IsEmpty ι]
    (x : EuclideanSpace ℝ ι) : Subsingleton (ball x r) :=
  Set.subsingleton_coe_of_subsingleton

theorem EuclideanSpace.volume_ball_lt_top [inst : NoAtoms (volume : Measure (EuclideanSpace ℝ ι))]
    (x : EuclideanSpace ℝ ι) : volume (ball x r) < ⊤ :=
  -- `volume` is finite on compacts, so this is mathlib's `MeasureTheory.measure_ball_lt_top`.
  measure_ball_lt_top
