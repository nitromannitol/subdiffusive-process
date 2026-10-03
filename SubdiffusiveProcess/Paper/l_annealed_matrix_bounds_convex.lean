module

public import SubdiffusiveProcess.Frozen.Section3.AnnealedMatrixBounds

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book
open scoped MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem l_annealed_matrix_bounds_convex {d : ℕ} :
    (∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (U : Ch02.Domain d)
        (m n : ℕ), n < m →
      Homogenization.MatLoewnerLE (abar M m U) (abar M n U) ∧
      Homogenization.MatLoewnerLE (abar M n U)
        ((∫ ω, cutoffRatioSup M n m U ω ∂M.P.toMeasure) • abar M m U) ∧
      Homogenization.MatLoewnerLE
        (Real.exp (-2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P *
          ((m - n : ℕ) : ℝ)) • abarStarInv M m U)
        (abarStarInv M n U) ∧
      Homogenization.MatLoewnerLE (abarStarInv M n U)
        ((∫ ω, cutoffRatioSup M m n U ω ∂M.P.toMeasure) • abarStarInv M m U)) ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m n : ℕ), n < m →
      ahom M m ≤ ahom M n ∧
      ahom M n ≤
        Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P *
          ((m - n : ℕ) : ℝ)) * ahom M m :=
  SubdiffusiveProcess.Frozen.Section3.annealed_matrix_bounds 

end Paper
