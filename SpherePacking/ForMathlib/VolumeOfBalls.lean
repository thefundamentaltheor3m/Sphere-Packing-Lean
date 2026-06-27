module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

@[expose] public section

/- This file contains several (semi-adhoc) lemmas about volume of balls, e.g. that they are positive
generally, or 0 over (ι → ℝ) if ι is Empty. -/

open Metric MeasureTheory MeasureSpace ENNReal

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
    (x : EuclideanSpace ℝ ι) : Subsingleton (ball x r) := by
  apply Subsingleton.intro
  intro ⟨x, _⟩ ⟨y, _⟩
  congr 1
  ext t
  exact False.elim (IsEmpty.false t)

theorem EuclideanSpace.volume_ball_lt_top [inst : NoAtoms (volume : Measure (EuclideanSpace ℝ ι))]
    (x : EuclideanSpace ℝ ι) : volume (ball x r) < ⊤ :=
  -- `volume` is finite on compacts, so this is mathlib's `MeasureTheory.measure_ball_lt_top`.
  measure_ball_lt_top
