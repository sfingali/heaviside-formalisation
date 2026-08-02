import Lake
open Lake DSL

package «heaviside-formalisation» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "f4570dc2f3c801ed0c0edd5867f943e2b84e4dec"

lean_lib «MyProof»
