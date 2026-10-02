import Lake
open Lake DSL

package subdiffusive_process

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"

require CoarseGraining from git
  "https://github.com/scottnarmstrong/CoarseGraining" @ "97d07f1d06d2028c9c9cbf2d63e6f9da3e6d4079"

require MarkovProcess from git
  "https://github.com/scottnarmstrong/MarkovProcess" @ "60a807e8305ae334de83d48a122ab4eb9ccc5481"

@[default_target]
lean_lib SubdiffusiveProcess where
  globs := #[.andSubmodules `SubdiffusiveProcess]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]

lean_lib SubdiffusiveProcessAudit where
  globs := #[.submodules `SubdiffusiveProcessAudit]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]
