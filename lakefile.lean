import Lake
open Lake DSL

package SpherePacking where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩, -- switch off auto-implicit
    ⟨`relaxedAutoImplicit, false⟩ -- switch off relaxed auto-implicit
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

@[default_target]
lean_lib SpherePacking
