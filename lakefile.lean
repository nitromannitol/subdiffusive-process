import Lake

open Lake DSL

package SubdiffusiveProcess

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0-rc2"

require CoarseGraining from git
  "https://github.com/scottnarmstrong/CoarseGraining" @ "df82db0a9e5ff2c11c5c6faa2777fd83bfdbb013"

require MarkovProcess from git
  "https://github.com/scottnarmstrong/MarkovProcess" @ "814b0f8820c2da712eb79574ea7ca3be8db4b69d"

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
