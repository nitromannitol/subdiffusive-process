module

public import MarkovProcess.Main
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Support

@[expose] public section

/-!
# The state space of the Section 7 diffusions

Support declaration for freeze package 05 (D-083): the frozen Section 7
statements refer to `State d` for the ambient space `Homogenization.Vec d`.
-/

/-- The state space of the Section 7 diffusions (freeze package 05, D-083). -/
abbrev SubdiffusiveProcess.Frozen.Section7.State (d : ℕ) := Homogenization.Vec d
