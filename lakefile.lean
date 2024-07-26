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

@[default_target]
lean_lib SpherePacking

lean_exe mk_all where
  srcDir := "scripts"
  supportInterpreter := true
  -- Executables which import `Lake` must set `-lLake`.
  weakLinkArgs := #["-lLake"]

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"
