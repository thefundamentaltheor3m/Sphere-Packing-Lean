import Mathlib.Tactic
import SpherePacking.Tactic.NormNumI

/-! See https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/AlphaEvolve.20Matmul.20Verification/with/519501658 -/

def matmul4x4 (A B : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=

  -- Linear combinations of elements from A
  let a0 := (0.5+0.5*Complex.I)*(A 0 0) + (0.5+0.5*Complex.I)*(A 0 1) + (0.5+-0.5*Complex.I)*(A 1 0) + (0.5+-0.5*Complex.I)*(A 1 1) + (0.5+-0.5*Complex.I)*(A 2 0) + (0.5+-0.5*Complex.I)*(A 2 1) + (0.5+-0.5*Complex.I)*(A 3 0) + (0.5+-0.5*Complex.I)*(A 3 1)
  let a1 := (0.5+0.5*Complex.I)*(A 0 0) + (-0.5+0.5*Complex.I)*(A 0 3) + (0.5+0.5*Complex.I)*(A 1 0) + (-0.5+0.5*Complex.I)*(A 1 3) + (-0.5+-0.5*Complex.I)*(A 2 0) + (0.5+-0.5*Complex.I)*(A 2 3) + (0.5+-0.5*Complex.I)*(A 3 0) + (0.5+0.5*Complex.I)*(A 3 3)
  let a2 := -0.5*(A 0 1) + 0.5*(A 0 2) + -0.5*Complex.I*(A 1 1) + 0.5*Complex.I*(A 1 2) + 0.5*Complex.I*(A 2 1) + -0.5*Complex.I*(A 2 2) + -0.5*Complex.I*(A 3 1) + 0.5*Complex.I*(A 3 2)
  let a3 := -0.5*Complex.I*(A 0 0) + -0.5*(A 0 1) + 0.5*(A 0 2) + -0.5*(A 0 3) + 0.5*Complex.I*(A 1 0) + -0.5*(A 1 1) + 0.5*(A 1 2) + 0.5*(A 1 3) + -0.5*Complex.I*(A 2 0) + -0.5*(A 2 1) + 0.5*(A 2 2) + -0.5*(A 2 3) + -0.5*(A 3 0) + -0.5*Complex.I*(A 3 1) + 0.5*Complex.I*(A 3 2) + 0.5*Complex.I*(A 3 3)
  let a4 := (0.5+0.5*Complex.I)*(A 0 0) + (-0.5+-0.5*Complex.I)*(A 0 1) + (-0.5+0.5*Complex.I)*(A 1 0) + (0.5+-0.5*Complex.I)*(A 1 1) + (-0.5+0.5*Complex.I)*(A 2 0) + (0.5+-0.5*Complex.I)*(A 2 1) + (0.5+-0.5*Complex.I)*(A 3 0) + (-0.5+0.5*Complex.I)*(A 3 1)
  let a5 := (0.5+-0.5*Complex.I)*(A 0 2) + (-0.5+-0.5*Complex.I)*(A 0 3) + (0.5+-0.5*Complex.I)*(A 1 2) + (-0.5+-0.5*Complex.I)*(A 1 3) + (-0.5+0.5*Complex.I)*(A 2 2) + (0.5+0.5*Complex.I)*(A 2 3) + (-0.5+-0.5*Complex.I)*(A 3 2) + (-0.5+0.5*Complex.I)*(A 3 3)
  let a6 := 0.5*Complex.I*(A 0 0) + 0.5*(A 0 3) + -0.5*(A 1 0) + 0.5*Complex.I*(A 1 3) + 0.5*(A 2 0) + -0.5*Complex.I*(A 2 3) + -0.5*(A 3 0) + 0.5*Complex.I*(A 3 3)
  let a7 := (0.5+0.5*Complex.I)*(A 0 0) + (-0.5+-0.5*Complex.I)*(A 0 1) + (-0.5+-0.5*Complex.I)*(A 1 0) + (0.5+0.5*Complex.I)*(A 1 1) + (-0.5+-0.5*Complex.I)*(A 2 0) + (0.5+0.5*Complex.I)*(A 2 1) + (-0.5+0.5*Complex.I)*(A 3 0) + (0.5+-0.5*Complex.I)*(A 3 1)
  let a8 := -0.5*Complex.I*(A 0 0) + -0.5*Complex.I*(A 0 1) + -0.5*(A 0 2) + -0.5*Complex.I*(A 0 3) + 0.5*(A 1 0) + 0.5*(A 1 1) + -0.5*Complex.I*(A 1 2) + 0.5*(A 1 3) + -0.5*(A 2 0) + -0.5*(A 2 1) + -0.5*Complex.I*(A 2 2) + 0.5*(A 2 3) + 0.5*(A 3 0) + 0.5*(A 3 1) + 0.5*Complex.I*(A 3 2) + -0.5*(A 3 3)
  let a9 := (-0.5+0.5*Complex.I)*(A 0 0) + (-0.5+-0.5*Complex.I)*(A 0 3) + (0.5+0.5*Complex.I)*(A 1 0) + (-0.5+0.5*Complex.I)*(A 1 3) + (-0.5+-0.5*Complex.I)*(A 2 0) + (0.5+-0.5*Complex.I)*(A 2 3) + (-0.5+-0.5*Complex.I)*(A 3 0) + (0.5+-0.5*Complex.I)*(A 3 3)
  let a10 := (-0.5+0.5*Complex.I)*(A 0 0) + (0.5+-0.5*Complex.I)*(A 0 1) + (-0.5+0.5*Complex.I)*(A 1 0) + (0.5+-0.5*Complex.I)*(A 1 1) + (0.5+-0.5*Complex.I)*(A 2 0) + (-0.5+0.5*Complex.I)*(A 2 1) + (0.5+0.5*Complex.I)*(A 3 0) + (-0.5+-0.5*Complex.I)*(A 3 1)
  let a11 := 0.5*(A 0 0) + 0.5*(A 0 1) + -0.5*Complex.I*(A 0 2) + -0.5*(A 0 3) + -0.5*(A 1 0) + -0.5*(A 1 1) + 0.5*Complex.I*(A 1 2) + 0.5*(A 1 3) + 0.5*(A 2 0) + 0.5*(A 2 1) + 0.5*Complex.I*(A 2 2) + 0.5*(A 2 3) + -0.5*Complex.I*(A 3 0) + -0.5*Complex.I*(A 3 1) + 0.5*(A 3 2) + -0.5*Complex.I*(A 3 3)
  let a12 := (0.5+0.5*Complex.I)*(A 0 1) + (-0.5+-0.5*Complex.I)*(A 0 2) + (-0.5+0.5*Complex.I)*(A 1 1) + (0.5+-0.5*Complex.I)*(A 1 2) + (-0.5+0.5*Complex.I)*(A 2 1) + (0.5+-0.5*Complex.I)*(A 2 2) + (0.5+-0.5*Complex.I)*(A 3 1) + (-0.5+0.5*Complex.I)*(A 3 2)
  let a13 := (0.5+-0.5*Complex.I)*(A 0 1) + (-0.5+0.5*Complex.I)*(A 0 2) + (0.5+-0.5*Complex.I)*(A 1 1) + (-0.5+0.5*Complex.I)*(A 1 2) + (0.5+-0.5*Complex.I)*(A 2 1) + (-0.5+0.5*Complex.I)*(A 2 2) + (0.5+0.5*Complex.I)*(A 3 1) + (-0.5+-0.5*Complex.I)*(A 3 2)
  let a14 := 0.5*Complex.I*(A 0 0) + -0.5*(A 0 1) + 0.5*(A 0 2) + -0.5*(A 0 3) + 0.5*(A 1 0) + -0.5*Complex.I*(A 1 1) + 0.5*Complex.I*(A 1 2) + 0.5*Complex.I*(A 1 3) + 0.5*(A 2 0) + 0.5*Complex.I*(A 2 1) + -0.5*Complex.I*(A 2 2) + 0.5*Complex.I*(A 2 3) + 0.5*(A 3 0) + -0.5*Complex.I*(A 3 1) + 0.5*Complex.I*(A 3 2) + 0.5*Complex.I*(A 3 3)
  let a15 := (-0.5+0.5*Complex.I)*(A 0 2) + (0.5+0.5*Complex.I)*(A 0 3) + (0.5+-0.5*Complex.I)*(A 1 2) + (-0.5+-0.5*Complex.I)*(A 1 3) + (0.5+-0.5*Complex.I)*(A 2 2) + (-0.5+-0.5*Complex.I)*(A 2 3) + (-0.5+-0.5*Complex.I)*(A 3 2) + (-0.5+0.5*Complex.I)*(A 3 3)
  let a16 := -0.5*(A 0 0) + 0.5*Complex.I*(A 0 1) + 0.5*Complex.I*(A 0 2) + -0.5*Complex.I*(A 0 3) + -0.5*(A 1 0) + -0.5*Complex.I*(A 1 1) + -0.5*Complex.I*(A 1 2) + -0.5*Complex.I*(A 1 3) + -0.5*(A 2 0) + 0.5*Complex.I*(A 2 1) + 0.5*Complex.I*(A 2 2) + -0.5*Complex.I*(A 2 3) + -0.5*Complex.I*(A 3 0) + 0.5*(A 3 1) + 0.5*(A 3 2) + 0.5*(A 3 3)
  let a17 := (0.5+0.5*Complex.I)*(A 0 0) + (0.5+0.5*Complex.I)*(A 0 1) + (0.5+0.5*Complex.I)*(A 1 0) + (0.5+0.5*Complex.I)*(A 1 1) + (0.5+0.5*Complex.I)*(A 2 0) + (0.5+0.5*Complex.I)*(A 2 1) + (-0.5+0.5*Complex.I)*(A 3 0) + (-0.5+0.5*Complex.I)*(A 3 1)
  let a18 := 0.5*Complex.I*(A 0 0) + 0.5*Complex.I*(A 0 1) + -0.5*(A 0 2) + 0.5*Complex.I*(A 0 3) + 0.5*Complex.I*(A 1 0) + 0.5*Complex.I*(A 1 1) + -0.5*(A 1 2) + 0.5*Complex.I*(A 1 3) + 0.5*Complex.I*(A 2 0) + 0.5*Complex.I*(A 2 1) + 0.5*(A 2 2) + -0.5*Complex.I*(A 2 3) + -0.5*(A 3 0) + -0.5*(A 3 1) + 0.5*Complex.I*(A 3 2) + 0.5*(A 3 3)
  let a19 := (0.5+-0.5*Complex.I)*(A 0 2) + (0.5+0.5*Complex.I)*(A 0 3) + (0.5+-0.5*Complex.I)*(A 1 2) + (0.5+0.5*Complex.I)*(A 1 3) + (0.5+-0.5*Complex.I)*(A 2 2) + (0.5+0.5*Complex.I)*(A 2 3) + (0.5+0.5*Complex.I)*(A 3 2) + (-0.5+0.5*Complex.I)*(A 3 3)
  let a20 := (0.5+0.5*Complex.I)*(A 0 1) + (-0.5+-0.5*Complex.I)*(A 0 2) + (0.5+0.5*Complex.I)*(A 1 1) + (-0.5+-0.5*Complex.I)*(A 1 2) + (-0.5+-0.5*Complex.I)*(A 2 1) + (0.5+0.5*Complex.I)*(A 2 2) + (0.5+-0.5*Complex.I)*(A 3 1) + (-0.5+0.5*Complex.I)*(A 3 2)
  let a21 := 0.5*Complex.I*(A 0 0) + -0.5*Complex.I*(A 0 1) + -0.5*(A 0 2) + -0.5*Complex.I*(A 0 3) + -0.5*Complex.I*(A 1 0) + 0.5*Complex.I*(A 1 1) + 0.5*(A 1 2) + 0.5*Complex.I*(A 1 3) + -0.5*Complex.I*(A 2 0) + 0.5*Complex.I*(A 2 1) + -0.5*(A 2 2) + -0.5*Complex.I*(A 2 3) + -0.5*(A 3 0) + 0.5*(A 3 1) + 0.5*Complex.I*(A 3 2) + -0.5*(A 3 3)
  let a22 := (-0.5+-0.5*Complex.I)*(A 0 0) + (-0.5+0.5*Complex.I)*(A 0 3) + (0.5+-0.5*Complex.I)*(A 1 0) + (-0.5+-0.5*Complex.I)*(A 1 3) + (0.5+-0.5*Complex.I)*(A 2 0) + (-0.5+-0.5*Complex.I)*(A 2 3) + (-0.5+0.5*Complex.I)*(A 3 0) + (0.5+0.5*Complex.I)*(A 3 3)
  let a23 := (-0.5+-0.5*Complex.I)*(A 0 2) + (0.5+-0.5*Complex.I)*(A 0 3) + (0.5+-0.5*Complex.I)*(A 1 2) + (0.5+0.5*Complex.I)*(A 1 3) + (0.5+-0.5*Complex.I)*(A 2 2) + (0.5+0.5*Complex.I)*(A 2 3) + (-0.5+0.5*Complex.I)*(A 3 2) + (-0.5+-0.5*Complex.I)*(A 3 3)
  let a24 := -0.5*(A 0 0) + 0.5*(A 0 1) + -0.5*Complex.I*(A 0 2) + -0.5*(A 0 3) + -0.5*Complex.I*(A 1 0) + 0.5*Complex.I*(A 1 1) + 0.5*(A 1 2) + -0.5*Complex.I*(A 1 3) + -0.5*Complex.I*(A 2 0) + 0.5*Complex.I*(A 2 1) + -0.5*(A 2 2) + 0.5*Complex.I*(A 2 3) + 0.5*Complex.I*(A 3 0) + -0.5*Complex.I*(A 3 1) + 0.5*(A 3 2) + -0.5*Complex.I*(A 3 3)
  let a25 := (0.5+-0.5*Complex.I)*(A 0 2) + (0.5+0.5*Complex.I)*(A 0 3) + (-0.5+-0.5*Complex.I)*(A 1 2) + (0.5+-0.5*Complex.I)*(A 1 3) + (0.5+0.5*Complex.I)*(A 2 2) + (-0.5+0.5*Complex.I)*(A 2 3) + (0.5+0.5*Complex.I)*(A 3 2) + (-0.5+0.5*Complex.I)*(A 3 3)
  let a26 := (0.5+0.5*Complex.I)*(A 0 1) + (0.5+0.5*Complex.I)*(A 0 2) + (-0.5+-0.5*Complex.I)*(A 1 1) + (-0.5+-0.5*Complex.I)*(A 1 2) + (0.5+0.5*Complex.I)*(A 2 1) + (0.5+0.5*Complex.I)*(A 2 2) + (0.5+-0.5*Complex.I)*(A 3 1) + (0.5+-0.5*Complex.I)*(A 3 2)
  let a27 := -0.5*Complex.I*(A 0 0) + -0.5*Complex.I*(A 0 1) + 0.5*(A 0 2) + 0.5*Complex.I*(A 0 3) + -0.5*(A 1 0) + -0.5*(A 1 1) + -0.5*Complex.I*(A 1 2) + 0.5*(A 1 3) + -0.5*(A 2 0) + -0.5*(A 2 1) + 0.5*Complex.I*(A 2 2) + -0.5*(A 2 3) + -0.5*(A 3 0) + -0.5*(A 3 1) + 0.5*Complex.I*(A 3 2) + -0.5*(A 3 3)
  let a28 := (-0.5+0.5*Complex.I)*(A 0 0) + (-0.5+0.5*Complex.I)*(A 0 1) + (-0.5+-0.5*Complex.I)*(A 1 0) + (-0.5+-0.5*Complex.I)*(A 1 1) + (0.5+0.5*Complex.I)*(A 2 0) + (0.5+0.5*Complex.I)*(A 2 1) + (-0.5+-0.5*Complex.I)*(A 3 0) + (-0.5+-0.5*Complex.I)*(A 3 1)
  let a29 := (0.5+0.5*Complex.I)*(A 0 0) + (0.5+-0.5*Complex.I)*(A 0 3) + (-0.5+-0.5*Complex.I)*(A 1 0) + (-0.5+0.5*Complex.I)*(A 1 3) + (0.5+0.5*Complex.I)*(A 2 0) + (0.5+-0.5*Complex.I)*(A 2 3) + (0.5+-0.5*Complex.I)*(A 3 0) + (-0.5+-0.5*Complex.I)*(A 3 3)
  let a30 := (0.5+0.5*Complex.I)*(A 0 1) + (0.5+0.5*Complex.I)*(A 0 2) + (-0.5+-0.5*Complex.I)*(A 1 1) + (-0.5+-0.5*Complex.I)*(A 1 2) + (-0.5+-0.5*Complex.I)*(A 2 1) + (-0.5+-0.5*Complex.I)*(A 2 2) + (-0.5+0.5*Complex.I)*(A 3 1) + (-0.5+0.5*Complex.I)*(A 3 2)
  let a31 := 0.5*(A 0 0) + -0.5*(A 0 1) + -0.5*Complex.I*(A 0 2) + 0.5*(A 0 3) + 0.5*(A 1 0) + -0.5*(A 1 1) + -0.5*Complex.I*(A 1 2) + 0.5*(A 1 3) + -0.5*(A 2 0) + 0.5*(A 2 1) + -0.5*Complex.I*(A 2 2) + 0.5*(A 2 3) + -0.5*Complex.I*(A 3 0) + 0.5*Complex.I*(A 3 1) + 0.5*(A 3 2) + 0.5*Complex.I*(A 3 3)
  let a32 := (0.5+0.5*Complex.I)*(A 0 2) + (0.5+-0.5*Complex.I)*(A 0 3) + (-0.5+0.5*Complex.I)*(A 1 2) + (0.5+0.5*Complex.I)*(A 1 3) + (0.5+-0.5*Complex.I)*(A 2 2) + (-0.5+-0.5*Complex.I)*(A 2 3) + (-0.5+0.5*Complex.I)*(A 3 2) + (0.5+0.5*Complex.I)*(A 3 3)
  let a33 := 0.5*(A 0 0) + 0.5*Complex.I*(A 0 1) + -0.5*Complex.I*(A 0 2) + -0.5*Complex.I*(A 0 3) + -0.5*(A 1 0) + 0.5*Complex.I*(A 1 1) + -0.5*Complex.I*(A 1 2) + 0.5*Complex.I*(A 1 3) + -0.5*(A 2 0) + -0.5*Complex.I*(A 2 1) + 0.5*Complex.I*(A 2 2) + 0.5*Complex.I*(A 2 3) + 0.5*Complex.I*(A 3 0) + 0.5*(A 3 1) + -0.5*(A 3 2) + 0.5*(A 3 3)
  let a34 := -0.5*Complex.I*(A 0 0) + 0.5*Complex.I*(A 0 1) + -0.5*(A 0 2) + 0.5*Complex.I*(A 0 3) + -0.5*(A 1 0) + 0.5*(A 1 1) + 0.5*Complex.I*(A 1 2) + 0.5*(A 1 3) + 0.5*(A 2 0) + -0.5*(A 2 1) + 0.5*Complex.I*(A 2 2) + 0.5*(A 2 3) + 0.5*(A 3 0) + -0.5*(A 3 1) + 0.5*Complex.I*(A 3 2) + 0.5*(A 3 3)
  let a35 := (0.5+-0.5*Complex.I)*(A 0 2) + (0.5+0.5*Complex.I)*(A 0 3) + (-0.5+0.5*Complex.I)*(A 1 2) + (-0.5+-0.5*Complex.I)*(A 1 3) + (0.5+-0.5*Complex.I)*(A 2 2) + (0.5+0.5*Complex.I)*(A 2 3) + (-0.5+-0.5*Complex.I)*(A 3 2) + (0.5+-0.5*Complex.I)*(A 3 3)
  let a36 := (-0.5+-0.5*Complex.I)*(A 0 1) + (-0.5+-0.5*Complex.I)*(A 0 2) + (-0.5+0.5*Complex.I)*(A 1 1) + (-0.5+0.5*Complex.I)*(A 1 2) + (0.5+-0.5*Complex.I)*(A 2 1) + (0.5+-0.5*Complex.I)*(A 2 2) + (0.5+-0.5*Complex.I)*(A 3 1) + (0.5+-0.5*Complex.I)*(A 3 2)
  let a37 := 0.5*(A 0 0) + -0.5*Complex.I*(A 0 1) + -0.5*Complex.I*(A 0 2) + -0.5*Complex.I*(A 0 3) + 0.5*Complex.I*(A 1 0) + -0.5*(A 1 1) + -0.5*(A 1 2) + 0.5*(A 1 3) + 0.5*Complex.I*(A 2 0) + 0.5*(A 2 1) + 0.5*(A 2 2) + 0.5*(A 2 3) + -0.5*Complex.I*(A 3 0) + 0.5*(A 3 1) + 0.5*(A 3 2) + -0.5*(A 3 3)
  let a38 := (0.5+-0.5*Complex.I)*(A 0 1) + (0.5+-0.5*Complex.I)*(A 0 2) + (-0.5+-0.5*Complex.I)*(A 1 1) + (-0.5+-0.5*Complex.I)*(A 1 2) + (-0.5+-0.5*Complex.I)*(A 2 1) + (-0.5+-0.5*Complex.I)*(A 2 2) + (-0.5+-0.5*Complex.I)*(A 3 1) + (-0.5+-0.5*Complex.I)*(A 3 2)
  let a39 := -0.5*(A 0 0) + -0.5*Complex.I*(A 0 1) + -0.5*Complex.I*(A 0 2) + -0.5*Complex.I*(A 0 3) + -0.5*(A 1 0) + 0.5*Complex.I*(A 1 1) + 0.5*Complex.I*(A 1 2) + -0.5*Complex.I*(A 1 3) + 0.5*(A 2 0) + 0.5*Complex.I*(A 2 1) + 0.5*Complex.I*(A 2 2) + 0.5*Complex.I*(A 2 3) + 0.5*Complex.I*(A 3 0) + 0.5*(A 3 1) + 0.5*(A 3 2) + -0.5*(A 3 3)
  let a40 := (-0.5+-0.5*Complex.I)*(A 0 0) + (-0.5+-0.5*Complex.I)*(A 0 1) + (0.5+0.5*Complex.I)*(A 1 0) + (0.5+0.5*Complex.I)*(A 1 1) + (-0.5+-0.5*Complex.I)*(A 2 0) + (-0.5+-0.5*Complex.I)*(A 2 1) + (-0.5+0.5*Complex.I)*(A 3 0) + (-0.5+0.5*Complex.I)*(A 3 1)
  let a41 := (0.5+-0.5*Complex.I)*(A 0 0) + (-0.5+-0.5*Complex.I)*(A 0 3) + (-0.5+0.5*Complex.I)*(A 1 0) + (0.5+0.5*Complex.I)*(A 1 3) + (-0.5+0.5*Complex.I)*(A 2 0) + (0.5+0.5*Complex.I)*(A 2 3) + (0.5+0.5*Complex.I)*(A 3 0) + (0.5+-0.5*Complex.I)*(A 3 3)
  let a42 := (0.5+0.5*Complex.I)*(A 0 0) + (-0.5+0.5*Complex.I)*(A 0 3) + (0.5+-0.5*Complex.I)*(A 1 0) + (0.5+0.5*Complex.I)*(A 1 3) + (0.5+-0.5*Complex.I)*(A 2 0) + (0.5+0.5*Complex.I)*(A 2 3) + (0.5+-0.5*Complex.I)*(A 3 0) + (0.5+0.5*Complex.I)*(A 3 3)
  let a43 := 0.5*Complex.I*(A 0 0) + 0.5*(A 0 1) + -0.5*(A 0 2) + -0.5*(A 0 3) + 0.5*(A 1 0) + 0.5*Complex.I*(A 1 1) + -0.5*Complex.I*(A 1 2) + 0.5*Complex.I*(A 1 3) + -0.5*(A 2 0) + 0.5*Complex.I*(A 2 1) + -0.5*Complex.I*(A 2 2) + -0.5*Complex.I*(A 2 3) + -0.5*(A 3 0) + -0.5*Complex.I*(A 3 1) + 0.5*Complex.I*(A 3 2) + -0.5*Complex.I*(A 3 3)
  let a44 := (0.5+-0.5*Complex.I)*(A 0 2) + (-0.5+-0.5*Complex.I)*(A 0 3) + (-0.5+-0.5*Complex.I)*(A 1 2) + (-0.5+0.5*Complex.I)*(A 1 3) + (-0.5+-0.5*Complex.I)*(A 2 2) + (-0.5+0.5*Complex.I)*(A 2 3) + (-0.5+-0.5*Complex.I)*(A 3 2) + (-0.5+0.5*Complex.I)*(A 3 3)
  let a45 := (-0.5+0.5*Complex.I)*(A 0 0) + (0.5+-0.5*Complex.I)*(A 0 1) + (0.5+0.5*Complex.I)*(A 1 0) + (-0.5+-0.5*Complex.I)*(A 1 1) + (-0.5+-0.5*Complex.I)*(A 2 0) + (0.5+0.5*Complex.I)*(A 2 1) + (-0.5+-0.5*Complex.I)*(A 3 0) + (0.5+0.5*Complex.I)*(A 3 1)
  let a46 := (0.5+-0.5*Complex.I)*(A 0 0) + (0.5+0.5*Complex.I)*(A 0 3) + (0.5+-0.5*Complex.I)*(A 1 0) + (0.5+0.5*Complex.I)*(A 1 3) + (0.5+-0.5*Complex.I)*(A 2 0) + (0.5+0.5*Complex.I)*(A 2 3) + (0.5+0.5*Complex.I)*(A 3 0) + (-0.5+0.5*Complex.I)*(A 3 3)
  let a47 := 0.5*(A 0 0) + 0.5*Complex.I*(A 0 1) + 0.5*Complex.I*(A 0 2) + -0.5*Complex.I*(A 0 3) + 0.5*Complex.I*(A 1 0) + 0.5*(A 1 1) + 0.5*(A 1 2) + 0.5*(A 1 3) + -0.5*Complex.I*(A 2 0) + 0.5*(A 2 1) + 0.5*(A 2 2) + -0.5*(A 2 3) + 0.5*Complex.I*(A 3 0) + 0.5*(A 3 1) + 0.5*(A 3 2) + 0.5*(A 3 3)

  -- Linear combinations of elements from B
  let b0 := -0.5*(B 0 0) + -0.5*(B 1 0) + 0.5*(B 2 0) + -0.5*Complex.I*(B 3 0)
  let b1 := 0.5*Complex.I*(B 0 1) + 0.5*Complex.I*(B 0 3) + 0.5*Complex.I*(B 1 1) + 0.5*Complex.I*(B 1 3) + 0.5*Complex.I*(B 2 1) + 0.5*Complex.I*(B 2 3) + 0.5*(B 3 1) + 0.5*(B 3 3)
  let b2 := (0.5+0.5*Complex.I)*(B 0 1) + (-0.5+-0.5*Complex.I)*(B 1 1) + (0.5+0.5*Complex.I)*(B 2 1) + (0.5+-0.5*Complex.I)*(B 3 1)
  let b3 := -0.5*Complex.I*(B 0 0) + 0.5*Complex.I*(B 0 2) + -0.5*Complex.I*(B 1 1) + -0.5*Complex.I*(B 1 2) + 0.5*Complex.I*(B 2 1) + 0.5*Complex.I*(B 2 2) + 0.5*(B 3 0) + -0.5*(B 3 2)
  let b4 := -0.5*(B 0 0) + 0.5*(B 0 2) + 0.5*(B 0 3) + 0.5*(B 1 0) + -0.5*(B 1 2) + -0.5*(B 1 3) + 0.5*(B 2 0) + -0.5*(B 2 2) + -0.5*(B 2 3) + 0.5*Complex.I*(B 3 0) + -0.5*Complex.I*(B 3 2) + -0.5*Complex.I*(B 3 3)
  let b5 := 0.5*(B 0 1) + 0.5*(B 0 3) + 0.5*(B 1 1) + 0.5*(B 1 3) + 0.5*(B 2 1) + 0.5*(B 2 3) + 0.5*Complex.I*(B 3 1) + 0.5*Complex.I*(B 3 3)
  let b6 := (-0.5+-0.5*Complex.I)*(B 0 1) + (0.5+0.5*Complex.I)*(B 1 1) + (0.5+0.5*Complex.I)*(B 2 1) + (0.5+-0.5*Complex.I)*(B 3 1)
  let b7 := -0.5*(B 0 0) + 0.5*(B 0 3) + 0.5*(B 1 0) + -0.5*(B 1 3) + -0.5*(B 2 0) + 0.5*(B 2 3) + 0.5*Complex.I*(B 3 0) + -0.5*Complex.I*(B 3 3)
  let b8 := 0.5*(B 0 0) + -0.5*(B 0 2) + -0.5*(B 0 3) + 0.5*(B 1 0) + -0.5*(B 1 2) + -0.5*(B 1 3) + 0.5*(B 2 1) + -0.5*Complex.I*(B 3 1)
  let b9 := 0.5*Complex.I*(B 0 1) + 0.5*Complex.I*(B 0 2) + 0.5*Complex.I*(B 0 3) + 0.5*Complex.I*(B 1 1) + 0.5*Complex.I*(B 1 2) + 0.5*Complex.I*(B 1 3) + -0.5*Complex.I*(B 2 1) + -0.5*Complex.I*(B 2 2) + -0.5*Complex.I*(B 2 3) + 0.5*(B 3 1) + 0.5*(B 3 2) + 0.5*(B 3 3)
  let b10 := 0.5*Complex.I*(B 0 1) + 0.5*Complex.I*(B 0 3) + -0.5*Complex.I*(B 1 1) + -0.5*Complex.I*(B 1 3) + -0.5*Complex.I*(B 2 1) + -0.5*Complex.I*(B 2 3) + -0.5*(B 3 1) + -0.5*(B 3 3)
  let b11 := -0.5*Complex.I*(B 0 0) + 0.5*Complex.I*(B 0 3) + -0.5*Complex.I*(B 1 0) + 0.5*Complex.I*(B 1 3) + 0.5*Complex.I*(B 2 1) + 0.5*Complex.I*(B 2 2) + -0.5*(B 3 1) + -0.5*(B 3 2)
  let b12 := -0.5*(B 0 0) + 0.5*(B 0 2) + 0.5*(B 0 3) + -0.5*(B 1 0) + 0.5*(B 1 2) + 0.5*(B 1 3) + 0.5*(B 2 0) + -0.5*(B 2 2) + -0.5*(B 2 3) + 0.5*Complex.I*(B 3 0) + -0.5*Complex.I*(B 3 2) + -0.5*Complex.I*(B 3 3)
  let b13 := 0.5*Complex.I*(B 0 0) + -0.5*Complex.I*(B 0 2) + -0.5*Complex.I*(B 1 0) + 0.5*Complex.I*(B 1 2) + 0.5*Complex.I*(B 2 0) + -0.5*Complex.I*(B 2 2) + -0.5*(B 3 0) + 0.5*(B 3 2)
  let b14 := -0.5*(B 0 1) + -0.5*(B 1 0) + 0.5*(B 2 0) + 0.5*Complex.I*(B 3 1)
  let b15 := 0.5*Complex.I*(B 0 0) + -0.5*Complex.I*(B 0 3) + 0.5*Complex.I*(B 1 0) + -0.5*Complex.I*(B 1 3) + -0.5*Complex.I*(B 2 0) + 0.5*Complex.I*(B 2 3) + 0.5*(B 3 0) + -0.5*(B 3 3)
  let b16 := 0.5*(B 0 1) + 0.5*(B 0 2) + 0.5*(B 1 0) + -0.5*(B 1 2) + 0.5*(B 2 0) + -0.5*(B 2 2) + -0.5*Complex.I*(B 3 1) + -0.5*Complex.I*(B 3 2)
  let b17 := -0.5*Complex.I*(B 0 0) + 0.5*Complex.I*(B 0 2) + -0.5*Complex.I*(B 1 0) + 0.5*Complex.I*(B 1 2) + -0.5*Complex.I*(B 2 0) + 0.5*Complex.I*(B 2 2) + 0.5*(B 3 0) + -0.5*(B 3 2)
  let b18 := -0.5*Complex.I*(B 0 1) + -0.5*Complex.I*(B 0 3) + -0.5*Complex.I*(B 1 1) + -0.5*Complex.I*(B 1 3) + -0.5*Complex.I*(B 2 0) + 0.5*Complex.I*(B 2 2) + 0.5*(B 3 0) + -0.5*(B 3 2)
  let b19 := -0.5*Complex.I*(B 0 0) + 0.5*Complex.I*(B 0 2) + 0.5*Complex.I*(B 1 0) + -0.5*Complex.I*(B 1 2) + 0.5*Complex.I*(B 2 0) + -0.5*Complex.I*(B 2 2) + 0.5*(B 3 0) + -0.5*(B 3 2)
  let b20 := -0.5*Complex.I*(B 0 1) + -0.5*Complex.I*(B 0 3) + -0.5*Complex.I*(B 1 1) + -0.5*Complex.I*(B 1 3) + 0.5*Complex.I*(B 2 1) + 0.5*Complex.I*(B 2 3) + 0.5*(B 3 1) + 0.5*(B 3 3)
  let b21 := -0.5*(B 0 1) + -0.5*(B 0 2) + 0.5*(B 1 1) + 0.5*(B 1 2) + -0.5*(B 2 0) + 0.5*(B 2 3) + 0.5*Complex.I*(B 3 0) + -0.5*Complex.I*(B 3 3)
  let b22 := -0.5*Complex.I*(B 0 0) + 0.5*Complex.I*(B 0 2) + 0.5*Complex.I*(B 0 3) + -0.5*Complex.I*(B 1 0) + 0.5*Complex.I*(B 1 2) + 0.5*Complex.I*(B 1 3) + -0.5*Complex.I*(B 2 0) + 0.5*Complex.I*(B 2 2) + 0.5*Complex.I*(B 2 3) + 0.5*(B 3 0) + -0.5*(B 3 2) + -0.5*(B 3 3)
  let b23 := -0.5*(B 0 0) + 0.5*(B 0 2) + 0.5*(B 0 3) + -0.5*(B 1 0) + 0.5*(B 1 2) + 0.5*(B 1 3) + -0.5*(B 2 0) + 0.5*(B 2 2) + 0.5*(B 2 3) + 0.5*Complex.I*(B 3 0) + -0.5*Complex.I*(B 3 2) + -0.5*Complex.I*(B 3 3)
  let b24 := 0.5*Complex.I*(B 0 1) + -0.5*Complex.I*(B 1 1) + -0.5*Complex.I*(B 2 0) + 0.5*Complex.I*(B 2 2) + 0.5*Complex.I*(B 2 3) + 0.5*(B 3 0) + -0.5*(B 3 2) + -0.5*(B 3 3)
  let b25 := 0.5*Complex.I*(B 0 1) + 0.5*Complex.I*(B 0 2) + 0.5*Complex.I*(B 0 3) + 0.5*Complex.I*(B 1 1) + 0.5*Complex.I*(B 1 2) + 0.5*Complex.I*(B 1 3) + -0.5*Complex.I*(B 2 1) + -0.5*Complex.I*(B 2 2) + -0.5*Complex.I*(B 2 3) + -0.5*(B 3 1) + -0.5*(B 3 2) + -0.5*(B 3 3)
  let b26 := 0.5*(B 0 1) + 0.5*(B 0 2) + -0.5*(B 1 1) + -0.5*(B 1 2) + -0.5*(B 2 1) + -0.5*(B 2 2) + -0.5*Complex.I*(B 3 1) + -0.5*Complex.I*(B 3 2)
  let b27 := 0.5*Complex.I*(B 0 1) + 0.5*Complex.I*(B 0 2) + 0.5*Complex.I*(B 0 3) + 0.5*Complex.I*(B 1 1) + 0.5*Complex.I*(B 1 2) + 0.5*Complex.I*(B 1 3) + -0.5*Complex.I*(B 2 0) + -0.5*(B 3 0)
  let b28 := 0.5*(B 0 1) + 0.5*(B 1 1) + 0.5*(B 2 1) + -0.5*Complex.I*(B 3 1)
  let b29 := 0.5*Complex.I*(B 0 1) + 0.5*Complex.I*(B 0 2) + -0.5*Complex.I*(B 1 1) + -0.5*Complex.I*(B 1 2) + 0.5*Complex.I*(B 2 1) + 0.5*Complex.I*(B 2 2) + -0.5*(B 3 1) + -0.5*(B 3 2)
  let b30 := -0.5*(B 0 0) + 0.5*(B 0 3) + -0.5*(B 1 0) + 0.5*(B 1 3) + -0.5*(B 2 0) + 0.5*(B 2 3) + 0.5*Complex.I*(B 3 0) + -0.5*Complex.I*(B 3 3)
  let b31 := 0.5*(B 0 0) + -0.5*(B 0 2) + -0.5*(B 1 0) + 0.5*(B 1 2) + -0.5*(B 2 1) + -0.5*(B 2 3) + 0.5*Complex.I*(B 3 1) + 0.5*Complex.I*(B 3 3)
  let b32 := 0.5*Complex.I*(B 0 1) + -0.5*Complex.I*(B 1 1) + -0.5*Complex.I*(B 2 1) + 0.5*(B 3 1)
  let b33 := -0.5*(B 0 1) + -0.5*(B 0 3) + 0.5*(B 1 0) + -0.5*(B 1 3) + -0.5*(B 2 0) + 0.5*(B 2 3) + -0.5*Complex.I*(B 3 1) + -0.5*Complex.I*(B 3 3)
  let b34 := 0.5*Complex.I*(B 0 0) + -0.5*Complex.I*(B 1 0) + 0.5*Complex.I*(B 2 1) + 0.5*Complex.I*(B 2 2) + 0.5*Complex.I*(B 2 3) + -0.5*(B 3 1) + -0.5*(B 3 2) + -0.5*(B 3 3)
  let b35 := -0.5*Complex.I*(B 0 1) + -0.5*Complex.I*(B 0 2) + 0.5*Complex.I*(B 1 1) + 0.5*Complex.I*(B 1 2) + -0.5*Complex.I*(B 2 1) + -0.5*Complex.I*(B 2 2) + -0.5*(B 3 1) + -0.5*(B 3 2)
  let b36 := -0.5*(B 0 1) + -0.5*(B 0 2) + -0.5*(B 0 3) + -0.5*(B 1 1) + -0.5*(B 1 2) + -0.5*(B 1 3) + -0.5*(B 2 1) + -0.5*(B 2 2) + -0.5*(B 2 3) + -0.5*Complex.I*(B 3 1) + -0.5*Complex.I*(B 3 2) + -0.5*Complex.I*(B 3 3)
  let b37 := 0.5*Complex.I*(B 0 1) + 0.5*Complex.I*(B 0 2) + 0.5*Complex.I*(B 0 3) + -0.5*Complex.I*(B 1 0) + 0.5*Complex.I*(B 1 2) + 0.5*Complex.I*(B 1 3) + -0.5*Complex.I*(B 2 0) + 0.5*Complex.I*(B 2 2) + 0.5*Complex.I*(B 2 3) + -0.5*(B 3 1) + -0.5*(B 3 2) + -0.5*(B 3 3)
  let b38 := 0.5*Complex.I*(B 0 0) + -0.5*Complex.I*(B 1 0) + -0.5*Complex.I*(B 2 0) + -0.5*(B 3 0)
  let b39 := -0.5*Complex.I*(B 0 0) + 0.5*Complex.I*(B 0 3) + 0.5*Complex.I*(B 1 1) + 0.5*Complex.I*(B 1 3) + 0.5*Complex.I*(B 2 1) + 0.5*Complex.I*(B 2 3) + -0.5*(B 3 0) + 0.5*(B 3 3)
  let b40 := 0.5*Complex.I*(B 0 1) + 0.5*Complex.I*(B 0 2) + 0.5*Complex.I*(B 1 1) + 0.5*Complex.I*(B 1 2) + -0.5*Complex.I*(B 2 1) + -0.5*Complex.I*(B 2 2) + 0.5*(B 3 1) + 0.5*(B 3 2)
  let b41 := 0.5*(B 0 0) + -0.5*(B 0 3) + 0.5*(B 1 0) + -0.5*(B 1 3) + -0.5*(B 2 0) + 0.5*(B 2 3) + 0.5*Complex.I*(B 3 0) + -0.5*Complex.I*(B 3 3)
  let b42 := 0.5*Complex.I*(B 0 0) + -0.5*Complex.I*(B 1 0) + 0.5*Complex.I*(B 2 0) + 0.5*(B 3 0)
  let b43 := 0.5*(B 0 0) + -0.5*(B 0 2) + -0.5*(B 0 3) + -0.5*(B 1 1) + -0.5*(B 1 2) + -0.5*(B 1 3) + 0.5*(B 2 1) + 0.5*(B 2 2) + 0.5*(B 2 3) + -0.5*Complex.I*(B 3 0) + 0.5*Complex.I*(B 3 2) + 0.5*Complex.I*(B 3 3)
  let b44 := -0.5*Complex.I*(B 0 0) + 0.5*Complex.I*(B 1 0) + -0.5*Complex.I*(B 2 0) + 0.5*(B 3 0)
  let b45 := -0.5*Complex.I*(B 0 1) + -0.5*Complex.I*(B 0 2) + -0.5*Complex.I*(B 0 3) + 0.5*Complex.I*(B 1 1) + 0.5*Complex.I*(B 1 2) + 0.5*Complex.I*(B 1 3) + -0.5*Complex.I*(B 2 1) + -0.5*Complex.I*(B 2 2) + -0.5*Complex.I*(B 2 3) + 0.5*(B 3 1) + 0.5*(B 3 2) + 0.5*(B 3 3)
  let b46 := -0.5*(B 0 0) + 0.5*(B 0 2) + 0.5*(B 1 0) + -0.5*(B 1 2) + 0.5*(B 2 0) + -0.5*(B 2 2) + 0.5*Complex.I*(B 3 0) + -0.5*Complex.I*(B 3 2)
  let b47 := 0.5*(B 0 0) + 0.5*(B 1 1) + 0.5*(B 2 1) + 0.5*Complex.I*(B 3 0)

  -- Perform the 48 multiplications
  let m0 := a0 * b0
  let m1 := a1 * b1
  let m2 := a2 * b2
  let m3 := a3 * b3
  let m4 := a4 * b4
  let m5 := a5 * b5
  let m6 := a6 * b6
  let m7 := a7 * b7
  let m8 := a8 * b8
  let m9 := a9 * b9
  let m10 := a10 * b10
  let m11 := a11 * b11
  let m12 := a12 * b12
  let m13 := a13 * b13
  let m14 := a14 * b14
  let m15 := a15 * b15
  let m16 := a16 * b16
  let m17 := a17 * b17
  let m18 := a18 * b18
  let m19 := a19 * b19
  let m20 := a20 * b20
  let m21 := a21 * b21
  let m22 := a22 * b22
  let m23 := a23 * b23
  let m24 := a24 * b24
  let m25 := a25 * b25
  let m26 := a26 * b26
  let m27 := a27 * b27
  let m28 := a28 * b28
  let m29 := a29 * b29
  let m30 := a30 * b30
  let m31 := a31 * b31
  let m32 := a32 * b32
  let m33 := a33 * b33
  let m34 := a34 * b34
  let m35 := a35 * b35
  let m36 := a36 * b36
  let m37 := a37 * b37
  let m38 := a38 * b38
  let m39 := a39 * b39
  let m40 := a40 * b40
  let m41 := a41 * b41
  let m42 := a42 * b42
  let m43 := a43 * b43
  let m44 := a44 * b44
  let m45 := a45 * b45
  let m46 := a46 * b46
  let m47 := a47 * b47

  -- Construct the result matrix
  let C00 := 0.5*Complex.I*m0 + -0.5*Complex.I*m1 + -0.5*m5 + 0.5*m8 + 0.5*Complex.I*m9 + (-0.5+0.5*Complex.I)*m11 + 0.5*m14 + -0.5*Complex.I*m15 + (-0.5+-0.5*Complex.I)*m16 + 0.5*Complex.I*m17 + (-0.5+-0.5*Complex.I)*m18 + -0.5*Complex.I*m24 + 0.5*Complex.I*m26 + 0.5*Complex.I*m27 + 0.5*m28 + 0.5*Complex.I*m30 + -0.5*Complex.I*m32 + 0.5*m34 + 0.5*m36 + -0.5*Complex.I*m37 + -0.5*m38 + (0.5+-0.5*Complex.I)*m39 + -0.5*Complex.I*m40 + -0.5*m42 + -0.5*m43 + -0.5*m44 + -0.5*Complex.I*m46 + 0.5*m47
  let C01 := -0.5*Complex.I*m0 + 0.5*m2 + (-0.5+-0.5*Complex.I)*m3 + 0.5*m5 + 0.5*m6 + -0.5*m8 + (0.5+-0.5*Complex.I)*m11 + -0.5*m12 + 0.5*Complex.I*m13 + 0.5*Complex.I*m14 + 0.5*Complex.I*m15 + -0.5*Complex.I*m17 + (0.5+0.5*Complex.I)*m18 + 0.5*m20 + -0.5*m22 + 0.5*Complex.I*m24 + -0.5*Complex.I*m27 + -0.5*m28 + -0.5*Complex.I*m29 + 0.5*Complex.I*m32 + (-0.5+-0.5*Complex.I)*m33 + -0.5*m34 + -0.5*m37 + 0.5*Complex.I*m40 + 0.5*Complex.I*m41 + -0.5*Complex.I*m43 + 0.5*m44 + -0.5*Complex.I*m47
  let C02 := -0.5*m2 + 0.5*m3 + -0.5*m5 + -0.5*Complex.I*m8 + 0.5*Complex.I*m11 + 0.5*m12 + -0.5*Complex.I*m13 + -0.5*Complex.I*m14 + -0.5*Complex.I*m15 + -0.5*m16 + -0.5*m18 + 0.5*Complex.I*m19 + -0.5*m20 + 0.5*Complex.I*m21 + -0.5*m23 + -0.5*Complex.I*m24 + -0.5*m25 + 0.5*Complex.I*m26 + 0.5*m27 + 0.5*Complex.I*m30 + -0.5*m31 + -0.5*Complex.I*m32 + 0.5*m33 + 0.5*m34 + 0.5*Complex.I*m35 + 0.5*m36 + -0.5*Complex.I*m37 + -0.5*m38 + -0.5*Complex.I*m39 + 0.5*Complex.I*m43 + -0.5*m44 + 0.5*m47
  let C03 := 0.5*Complex.I*m0 + -0.5*Complex.I*m1 + 0.5*Complex.I*m3 + -0.5*Complex.I*m4 + -0.5*m6 + 0.5*m7 + 0.5*m8 + 0.5*Complex.I*m9 + -0.5*m10 + -0.5*m11 + 0.5*m14 + -0.5*Complex.I*m16 + 0.5*Complex.I*m17 + -0.5*Complex.I*m18 + -0.5*m21 + 0.5*m22 + 0.5*m24 + 0.5*Complex.I*m27 + 0.5*m28 + 0.5*Complex.I*m29 + -0.5*Complex.I*m31 + 0.5*Complex.I*m33 + 0.5*Complex.I*m34 + 0.5*m37 + 0.5*m39 + -0.5*Complex.I*m40 + -0.5*Complex.I*m41 + -0.5*m42 + -0.5*m43 + -0.5*Complex.I*m45 + -0.5*Complex.I*m46 + 0.5*Complex.I*m47
  let C10 := -0.5*m0 + -0.5*m1 + -0.5*m5 + -0.5*Complex.I*m8 + -0.5*Complex.I*m9 + (0.5+-0.5*Complex.I)*m11 + -0.5*Complex.I*m14 + 0.5*Complex.I*m15 + (-0.5+0.5*Complex.I)*m16 + 0.5*Complex.I*m17 + (-0.5+-0.5*Complex.I)*m18 + -0.5*m24 + 0.5*m26 + -0.5*m27 + -0.5*Complex.I*m28 + 0.5*m30 + -0.5*m32 + 0.5*Complex.I*m34 + 0.5*m36 + -0.5*m37 + -0.5*m38 + (-0.5+-0.5*Complex.I)*m39 + 0.5*Complex.I*m40 + 0.5*m42 + 0.5*Complex.I*m43 + -0.5*Complex.I*m44 + -0.5*m46 + -0.5*Complex.I*m47
  let C11 := 0.5*m0 + -0.5*m2 + (0.5+-0.5*Complex.I)*m3 + 0.5*m5 + 0.5*m6 + 0.5*Complex.I*m8 + (-0.5+0.5*Complex.I)*m11 + 0.5*m12 + -0.5*m13 + -0.5*m14 + -0.5*Complex.I*m15 + -0.5*Complex.I*m17 + (0.5+0.5*Complex.I)*m18 + 0.5*Complex.I*m20 + -0.5*m22 + 0.5*m24 + 0.5*m27 + 0.5*Complex.I*m28 + 0.5*m29 + 0.5*m32 + (0.5+-0.5*Complex.I)*m33 + -0.5*Complex.I*m34 + -0.5*Complex.I*m37 + -0.5*Complex.I*m40 + -0.5*m41 + 0.5*m43 + 0.5*Complex.I*m44 + 0.5*m47
  let C12 := 0.5*m2 + -0.5*m3 + -0.5*m5 + -0.5*m8 + -0.5*Complex.I*m11 + -0.5*m12 + 0.5*m13 + 0.5*m14 + 0.5*Complex.I*m15 + -0.5*m16 + -0.5*m18 + 0.5*Complex.I*m19 + -0.5*Complex.I*m20 + -0.5*Complex.I*m21 + 0.5*Complex.I*m23 + -0.5*m24 + -0.5*Complex.I*m25 + 0.5*m26 + 0.5*Complex.I*m27 + 0.5*m30 + -0.5*m31 + -0.5*m32 + -0.5*m33 + 0.5*Complex.I*m34 + -0.5*Complex.I*m35 + 0.5*m36 + -0.5*m37 + -0.5*m38 + -0.5*Complex.I*m39 + -0.5*m43 + -0.5*Complex.I*m44 + -0.5*Complex.I*m47
  let C13 := -0.5*m0 + -0.5*m1 + 0.5*Complex.I*m3 + -0.5*m4 + -0.5*m6 + -0.5*m7 + -0.5*Complex.I*m8 + -0.5*Complex.I*m9 + -0.5*m10 + 0.5*m11 + -0.5*Complex.I*m14 + 0.5*Complex.I*m16 + 0.5*Complex.I*m17 + -0.5*Complex.I*m18 + 0.5*m21 + 0.5*m22 + -0.5*Complex.I*m24 + -0.5*m27 + -0.5*Complex.I*m28 + -0.5*m29 + -0.5*Complex.I*m31 + 0.5*Complex.I*m33 + -0.5*m34 + 0.5*Complex.I*m37 + -0.5*m39 + 0.5*Complex.I*m40 + 0.5*m41 + 0.5*m42 + 0.5*Complex.I*m43 + 0.5*m45 + -0.5*m46 + -0.5*m47
  let C20 := -0.5*Complex.I*m0 + 0.5*Complex.I*m1 + 0.5*Complex.I*m5 + -0.5*Complex.I*m8 + 0.5*m9 + (0.5+0.5*Complex.I)*m11 + 0.5*Complex.I*m14 + -0.5*m15 + (-0.5+-0.5*Complex.I)*m16 + 0.5*m17 + (-0.5+0.5*Complex.I)*m18 + -0.5*m24 + 0.5*Complex.I*m26 + 0.5*m27 + -0.5*m28 + -0.5*Complex.I*m30 + -0.5*Complex.I*m32 + -0.5*Complex.I*m34 + -0.5*Complex.I*m36 + -0.5*m37 + -0.5*Complex.I*m38 + (-0.5+0.5*Complex.I)*m39 + -0.5*m40 + -0.5*Complex.I*m42 + 0.5*Complex.I*m43 + -0.5*m44 + -0.5*Complex.I*m46 + 0.5*Complex.I*m47
  let C21 := 0.5*Complex.I*m0 + 0.5*Complex.I*m2 + (-0.5+-0.5*Complex.I)*m3 + -0.5*Complex.I*m5 + 0.5*Complex.I*m6 + 0.5*Complex.I*m8 + (-0.5+-0.5*Complex.I)*m11 + 0.5*Complex.I*m12 + 0.5*Complex.I*m13 + -0.5*m14 + 0.5*m15 + -0.5*m17 + (0.5+-0.5*Complex.I)*m18 + -0.5*m20 + 0.5*Complex.I*m22 + 0.5*m24 + -0.5*m27 + 0.5*m28 + -0.5*Complex.I*m29 + 0.5*Complex.I*m32 + (0.5+0.5*Complex.I)*m33 + 0.5*Complex.I*m34 + 0.5*Complex.I*m37 + 0.5*m40 + -0.5*Complex.I*m41 + -0.5*m43 + 0.5*m44 + 0.5*m47
  let C22 := -0.5*Complex.I*m2 + 0.5*m3 + 0.5*Complex.I*m5 + 0.5*m8 + 0.5*Complex.I*m11 + -0.5*Complex.I*m12 + -0.5*Complex.I*m13 + 0.5*m14 + -0.5*m15 + -0.5*m16 + -0.5*m18 + -0.5*m19 + 0.5*m20 + -0.5*Complex.I*m21 + 0.5*m23 + -0.5*m24 + 0.5*m25 + 0.5*Complex.I*m26 + 0.5*Complex.I*m27 + -0.5*Complex.I*m30 + 0.5*m31 + -0.5*Complex.I*m32 + -0.5*m33 + -0.5*Complex.I*m34 + -0.5*m35 + -0.5*Complex.I*m36 + -0.5*m37 + -0.5*Complex.I*m38 + 0.5*Complex.I*m39 + 0.5*m43 + -0.5*m44 + 0.5*Complex.I*m47
  let C23 := -0.5*Complex.I*m0 + 0.5*Complex.I*m1 + 0.5*Complex.I*m3 + -0.5*Complex.I*m4 + -0.5*Complex.I*m6 + 0.5*Complex.I*m7 + -0.5*Complex.I*m8 + 0.5*m9 + -0.5*Complex.I*m10 + 0.5*m11 + 0.5*Complex.I*m14 + -0.5*Complex.I*m16 + 0.5*m17 + 0.5*Complex.I*m18 + -0.5*m21 + -0.5*Complex.I*m22 + 0.5*Complex.I*m24 + 0.5*m27 + -0.5*m28 + 0.5*Complex.I*m29 + -0.5*Complex.I*m31 + -0.5*Complex.I*m33 + -0.5*m34 + -0.5*Complex.I*m37 + -0.5*m39 + -0.5*m40 + 0.5*Complex.I*m41 + -0.5*Complex.I*m42 + 0.5*Complex.I*m43 + -0.5*Complex.I*m45 + -0.5*Complex.I*m46 + -0.5*m47
  let C30 := -0.5*Complex.I*m0 + -0.5*Complex.I*m1 + 0.5*m5 + 0.5*Complex.I*m8 + 0.5*Complex.I*m9 + (-0.5+0.5*Complex.I)*m11 + -0.5*Complex.I*m14 + -0.5*Complex.I*m15 + (0.5+0.5*Complex.I)*m16 + -0.5*Complex.I*m17 + (0.5+0.5*Complex.I)*m18 + 0.5*m24 + -0.5*Complex.I*m26 + 0.5*m27 + 0.5*m28 + 0.5*Complex.I*m30 + 0.5*Complex.I*m32 + -0.5*Complex.I*m34 + -0.5*m36 + 0.5*m37 + -0.5*m38 + (0.5+-0.5*Complex.I)*m39 + -0.5*Complex.I*m40 + 0.5*m42 + -0.5*Complex.I*m43 + -0.5*m44 + 0.5*Complex.I*m46 + -0.5*Complex.I*m47
  let C31 := 0.5*Complex.I*m0 + -0.5*m2 + (-0.5+-0.5*Complex.I)*m3 + -0.5*m5 + 0.5*m6 + -0.5*Complex.I*m8 + (0.5+-0.5*Complex.I)*m11 + -0.5*m12 + 0.5*Complex.I*m13 + -0.5*m14 + 0.5*Complex.I*m15 + 0.5*Complex.I*m17 + (-0.5+-0.5*Complex.I)*m18 + -0.5*m20 + 0.5*m22 + -0.5*m24 + -0.5*m27 + -0.5*m28 + -0.5*Complex.I*m29 + -0.5*Complex.I*m32 + (0.5+0.5*Complex.I)*m33 + 0.5*Complex.I*m34 + 0.5*Complex.I*m37 + 0.5*Complex.I*m40 + -0.5*Complex.I*m41 + -0.5*m43 + 0.5*m44 + 0.5*m47
  let C32 := 0.5*m2 + 0.5*Complex.I*m3 + 0.5*m5 + -0.5*m8 + -0.5*m11 + 0.5*m12 + -0.5*Complex.I*m13 + 0.5*m14 + -0.5*Complex.I*m15 + 0.5*Complex.I*m16 + 0.5*Complex.I*m18 + 0.5*Complex.I*m19 + 0.5*m20 + 0.5*m21 + -0.5*m23 + 0.5*m24 + 0.5*m25 + -0.5*Complex.I*m26 + 0.5*Complex.I*m27 + 0.5*Complex.I*m30 + -0.5*Complex.I*m31 + 0.5*Complex.I*m32 + -0.5*Complex.I*m33 + -0.5*Complex.I*m34 + -0.5*Complex.I*m35 + -0.5*m36 + 0.5*m37 + -0.5*m38 + 0.5*m39 + 0.5*m43 + -0.5*m44 + -0.5*Complex.I*m47
  let C33 := -0.5*Complex.I*m0 + -0.5*Complex.I*m1 + 0.5*m3 + 0.5*Complex.I*m4 + -0.5*m6 + -0.5*m7 + 0.5*Complex.I*m8 + 0.5*Complex.I*m9 + -0.5*m10 + 0.5*Complex.I*m11 + -0.5*Complex.I*m14 + 0.5*m16 + -0.5*Complex.I*m17 + 0.5*m18 + -0.5*Complex.I*m21 + -0.5*m22 + -0.5*Complex.I*m24 + 0.5*m27 + 0.5*m28 + 0.5*Complex.I*m29 + -0.5*m31 + -0.5*m33 + -0.5*m34 + -0.5*Complex.I*m37 + -0.5*Complex.I*m39 + -0.5*Complex.I*m40 + 0.5*Complex.I*m41 + 0.5*m42 + -0.5*Complex.I*m43 + -0.5*Complex.I*m45 + 0.5*Complex.I*m46 + -0.5*m47

  !![C00, C01, C02, C03; C10, C11, C12, C13; C20, C21, C22, C23; C30, C31, C32, C33]

set_option maxHeartbeats 0


theorem check (A B : Matrix (Fin 4) (Fin 4) ℂ) : matmul4x4 A B = A * B := by
  -- expand A, B into their entries
  let a00 := A 0 0
  let a01 := A 0 1
  let a02 := A 0 2
  let a03 := A 0 3
  let a10 := A 1 0
  let a11 := A 1 1
  let a12 := A 1 2
  let a13 := A 1 3
  let a20 := A 2 0
  let a21 := A 2 1
  let a22 := A 2 2
  let a23 := A 2 3
  let a30 := A 3 0
  let a31 := A 3 1
  let a32 := A 3 2
  let a33 := A 3 3

  let b00 := B 0 0
  let b01 := B 0 1
  let b02 := B 0 2
  let b03 := B 0 3
  let b10 := B 1 0
  let b11 := B 1 1
  let b12 := B 1 2
  let b13 := B 1 3
  let b20 := B 2 0
  let b21 := B 2 1
  let b22 := B 2 2
  let b23 := B 2 3
  let b30 := B 3 0
  let b31 := B 3 1
  let b32 := B 3 2
  let b33 := B 3 3

  have hA : A = !![a00, a01, a02, a03; a10, a11, a12, a13; a20, a21, a22, a23; a30, a31, a32, a33] := by
    ext i j
    fin_cases i, j
    <;> rfl

  have hB : B = !![b00, b01, b02, b03; b10, b11, b12, b13; b20, b21, b22, b23; b30, b31, b32, b33] := by
    ext i j
    fin_cases i, j
    <;> rfl

  rw [hA, hB]

  -- to prove the two matrices are equal, we check each entries
  apply Eq.symm
  apply Matrix.ext
  intro i j
  fin_cases i, j <;>
  norm_num1 <;>
  stop
  { -- all_goals
    rw [Matrix.mul_apply]
    simp [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
    dsimp [matmul4x4]
    simp [
      add_zero, ← add_assoc, Mathlib.Tactic.RingNF.add_neg,
      mul_one, ← mul_assoc, mul_neg,
      left_distrib, right_distrib,
      Complex.I_mul_I,
    ]
    -- ring
    -- simp [Complex.I_sq, left_distrib]
    · norm_num1
      field_simp
      sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
  }
  <;> sorry
