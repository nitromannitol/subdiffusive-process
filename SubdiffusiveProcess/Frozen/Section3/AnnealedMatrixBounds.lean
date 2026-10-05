module

public import SubdiffusiveProcess.Providers.Section3.AnnealedMatrixBounds

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book
open scoped MatrixOrder


theorem SubdiffusiveProcess.Frozen.Section3.annealed_matrix_bounds {d : ℕ} :
    (∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (U : Ch02.Domain d)
        (m n : ℕ), n < m →
      Homogenization.MatLoewnerLE (abar M m U) (abar M n U) ∧
      Homogenization.MatLoewnerLE (abar M n U)
        ((∫ ω, cutoffRatioSup M n m U ω ∂M.P.toMeasure) • abar M m U) ∧
      Homogenization.MatLoewnerLE
        (Real.exp (-2 * _root_.SubdiffusiveProcess.Model.tauSq M.P *
          ((m - n : ℕ) : ℝ)) • abarStarInv M m U)
        (abarStarInv M n U) ∧
      Homogenization.MatLoewnerLE (abarStarInv M n U)
        ((∫ ω, cutoffRatioSup M m n U ω ∂M.P.toMeasure) • abarStarInv M m U)) ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m n : ℕ), n < m →
      ahom M m ≤ ahom M n ∧
      ahom M n ≤
        Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P *
          ((m - n : ℕ) : ℝ)) * ahom M m

:= SubdiffusiveProcess.Providers.Section3.annealed_matrix_bounds
