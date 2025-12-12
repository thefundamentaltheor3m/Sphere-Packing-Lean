import Mathlib.Analysis.Calculus.ContDiff.Operations

variable {𝕜 E F 𝔸 : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {s : Set E} {n : WithTop ℕ∞} [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸] {f g : E → F → 𝔸} {h : E → F}

/-- Compositional version of `ContDiffOn.mul` for use by `fun_prop`. -/
@[fun_prop]
theorem ContDiffOn.mul' (hf : ContDiffOn 𝕜 n ↿f (s ×ˢ .univ)) (hg : ContDiffOn 𝕜 n ↿g (s ×ˢ .univ))
    (hh : ContDiffOn 𝕜 n h s) :
    ContDiffOn 𝕜 n (fun x => (f x * g x) (h x)) s :=
  let hp := contDiffOn_id.prodMk hh
  (hf.comp hp fun _ hx => ⟨hx, trivial⟩).mul (hg.comp hp fun _ hx => ⟨hx, trivial⟩)
