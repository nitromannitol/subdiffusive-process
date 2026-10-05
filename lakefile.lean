import Lake

open Lake DSL

package SubdiffusiveProcess

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0-rc2"

require CoarseGraining from git
  "https://github.com/scottnarmstrong/CoarseGraining" @ "310d1a6bab3ba2d398cdaffec32f3c9d4b5a24be"

require MarkovProcess from git
  "https://github.com/scottnarmstrong/MarkovProcess" @ "666cda029098a1106914fc9fa7abd1727573284a"

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
    ⟨`linter.deprecated, true⟩,
    ⟨`warn.classDefReducibility, false⟩
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
    ⟨`linter.deprecated, true⟩,
    ⟨`warn.classDefReducibility, false⟩
  ]
