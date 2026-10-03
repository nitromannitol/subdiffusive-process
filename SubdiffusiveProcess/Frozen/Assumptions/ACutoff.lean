module

public import SubdiffusiveProcess.Frozen.Assumptions.GMCModel

@[expose] public section

/-!
# Finite-scale coefficient cutoff
-/

open Homogenization
open scoped BigOperators




noncomputable def SubdiffusiveProcess.Frozen.Assumptions.aCutoff {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (x : Vec d) : ℝ :=
  Real.exp
    (∑ k ∈ Finset.range (L + 1),
      (ω k x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))

