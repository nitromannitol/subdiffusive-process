module

public import Lake
public meta import Lake

@[expose] public section

open Lake DSL

package subdiffusive_process

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0-rc2"

require CoarseGraining from git
  "https://github.com/nitromannitol/CoarseGraining.git" @ "a8544b022a841efe05333645856b9fcc66ef7343"

require MarkovProcess from git
  "https://github.com/nitromannitol/MarkovProcess.git" @ "814b0f8820c2da712eb79574ea7ca3be8db4b69d"

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
