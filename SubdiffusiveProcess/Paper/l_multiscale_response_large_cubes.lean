module

public import SubdiffusiveProcess.Section4.MultiscaleResponseLargeCubes

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Lemma `l.multiscale.response.large.cubes`.

Correspondence with the live paper statement:
* `𝓔_{s,∞,r}(U; a_L, ahom_L)` for a translate `U = z + cu_K` (`K ≥ L`, `z` an arbitrary real translation)
  is `translatedHomogenizationErrorRandom M L K z s r`: the error of `cu_K` for the translated coefficient
  `a_L(z + ·)`, `p = ∞`, `q = r`.
* `S(m0, ξ, δ1)` is `inductionHypothesis M m0 ξ δ1`; `δ1 ∈ [δ², 1)` and `L ≤ m0` are literal.
* the bound is `C * s^{-1/r} * δ1^{1/2}`. -/
theorem l_multiscale_response_large_cubes {d : ℕ} :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (L m0 : ℕ) (s delta1 ξ : ℝ),
        0 < s → s ≤ 1 → M.delta ^ 2 ≤ delta1 → delta1 < 1 →
        L ≤ m0 →
        4 * (d : ℝ) * s⁻¹ ≤ ξ →
        ξ ≤ c * s * (M.delta ^ 2)⁻¹ * delta1 →
        inductionHypothesis M m0 ξ delta1 →
        ∀ K : ℕ, L ≤ K → ∀ z : PaperCubeTranslate d, ∀ r : ℕ,
          (r = 1 ∨ r = 2) →
          paperENNRealLpNorm M.P.toMeasure ξ
              (translatedHomogenizationErrorRandom M L K z s r) ≤
            ENNReal.ofReal
              (C * Real.rpow s (-(1 / (r : ℝ))) * Real.sqrt delta1)
    := _root_.SubdiffusiveProcess.Section4.multiscale_response_large_cubes

end SubdiffusiveProcess.Paper
