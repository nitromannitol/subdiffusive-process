module

public import SubdiffusiveProcess.Model.GMCModel

@[expose] public section

/-!
# Finite-scale coefficient cutoff
-/

open Homogenization
open scoped BigOperators

/-- The finite mean-one cutoff
`a_L(x) = exp (∑_{k=0}^L (g_k(x) - τ²))`, paper label `e.intro.cutoff.coefficients`. -/

noncomputable def SubdiffusiveProcess.Model.aCutoff {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) : ℝ :=
  Real.exp
    (∑ k ∈ Finset.range (L + 1),
      (ω k x - _root_.SubdiffusiveProcess.Model.tauSq M.P))

