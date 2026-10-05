module

public import SubdiffusiveProcess.Section5.RenormalizedDiffusivities

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Theorem `t.renormalized.diffusivities`.

Correspondence with the live paper statement:
* `η_sub = η_sub(d, law(g0))` is `∃ eta` after `∀ M`; the perturbative `δ0(d), C(d)` are chosen before `M`.
* The summary display for `0 ≤ n ≤ m` is the four-part conjunction; `min {1, e^{2τ²(m-n)} ahom_m}`
  is `min 1 (exp (2 τ² (m-n)) * ahom M m)`.
* the two-dimensional identity is `d = 2 → ahom M m = exp (-(m+1) τ²)`. -/
theorem t_renormalized_diffusivities {d : ℕ} :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
        ∃ eta : ℝ, 0 < eta ∧
          (∀ n m : ℕ, n ≤ m →
            Real.exp (-(m + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) ≤
                ahom M m ∧
            ahom M m ≤ ahom M n ∧
            ahom M n ≤ min 1
              (Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P *
                ((m - n : ℕ) : ℝ)) * ahom M m) ∧
            ahom M m ≤ Real.rpow 3 (-eta * (m + 1 : ℝ))) ∧
          (d = 2 → ∀ m : ℕ,
            ahom M m =
              Real.exp (-(m + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) ∧
          (M.delta ≤ delta0 → ∀ m : ℕ,
            |Real.log (ahom M m) +
                2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (m + 1 : ℝ) / d| ≤
              C * M.delta ^ 2 * |Real.log M.delta| *
                (1 + (m : ℝ) * M.delta))
    := _root_.SubdiffusiveProcess.Section5.renormalized_diffusivities

end SubdiffusiveProcess.Paper
