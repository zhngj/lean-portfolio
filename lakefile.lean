import Lake
open Lake DSL

package «LeanPortfolio» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "9944fe2973b8dc0b86949101ed98232c07cd54a0"

@[default_target]
lean_lib «Portfolio» where
