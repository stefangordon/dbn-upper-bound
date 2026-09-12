import Lake
open Lake DSL

/-- Lean 4 formalization of the de Bruijn–Newman upper bound
`Λ ≤ 3885632262767861213460393068710302759 / 24646172707879668706230182733520000000`.

Depends on Mathlib (v4.33.1) and on `alerad/leancert` (Apache-2.0), whose `LeanCert.Analysis.DBN`
library supplies the heat-flow analysis (Hadamard product, strip contraction, `Λ > -∞`,
`H₀ = ξ((1+iz)/2)/8`) used in `DBN.External`. -/
package «dbn» where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.1"

require leancert from git
  "https://github.com/alerad/leancert" @ "4ea18bb66dfcd7f18f260bc25302400f5a3cafd7"

@[default_target]
lean_lib «DBN» where
  globs := #[.andSubmodules `DBN]
