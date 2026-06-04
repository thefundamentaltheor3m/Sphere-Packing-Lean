# [Issue #400](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/issues/400)

This is suspicious:

gauss2/SpherePacking/CohnElkies/PoissonSummationLattices

/PoissonSummation.lean

around line 154

/-- iocCube is null-measurable (useful for integrals over its indicator). -/
public lemma nullMeasurableSet_iocCube : NullMeasurableSet (iocCube (d := d)) :=
(measurableSet_iocCube (d := d)).nullMeasurableSet

Most likely this is not needed. The half-open cube is already a measurable set. Why proving a weaker property?
