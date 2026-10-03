module

public import SubdiffusiveProcess.Frozen.Section4.EllipticityBound

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Lemma `l.ellipticity.bound`.

Correspondence with the live paper statement:
* `S(m0, ξ, δ1)` is `inductionHypothesis M m0 ξ δ1` (Definition `d.mathcalS.def`; it carries `1 ≤ ξ`,
  `0 < δ1 < 1`, the domain of the paper's definition).
* the supremum over `L ≥ m` and over the cubes `z + cu_n`, `z ∈ 3^n ℤ^d ∩ cu_m`, of
  `𝓔_{s,∞}(z+cu_n; a_L, (b_{L,m})_{cu_m})` is `ellipticityMomentObservable M m n s` (Definition
  `d.bLm`: `tailCoefficient`; `(b_{L,m})_{cu_m}` its normalized cube average).
* `(e.mathcal.E.Lms.moments.small.L)` is the second conjunct (`L ≤ m0`).
* `c(d) ∈ (0,1]`, `C(d) ∈ [1,∞)` are fixed before `M, m0, ξ, δ1, s, m, n`. -/
theorem l_ellipticity_bound {d : ℕ} :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1 ∧ 1 ≤ C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (m0 : ℕ) (ξ delta1 : ℝ),
        6 ≤ ξ → M.delta ^ 2 ≤ delta1 → delta1 < 1 →
        inductionHypothesis M m0 ξ delta1 →
        ∀ s : ℝ, 0 < s → s ≤ 1 →
          4 * (d : ℝ) * s⁻¹ ≤ ξ →
          ξ ≤ c * s * (M.delta ^ 2)⁻¹ * delta1 →
          (∀ (m : ℕ) (n : ℤ), n ≤ (m0 : ℤ) → n ≤ (m : ℤ) →
            paperENNRealLpNorm M.P.toMeasure ξ
                (ellipticityMomentObservable M m n s) ≤
              ENNReal.ofReal
                (C * s⁻¹ * Real.sqrt delta1 *
                  Real.rpow 3
                    (((d : ℝ) / ξ + s / 2) * (((m : ℤ) - n : ℤ) : ℝ)))) ∧
          (∀ L : ℕ, L ≤ m0 →
            paperENNRealLpNorm M.P.toMeasure ξ
                (homogenizationErrorRandom M L L s) ≤
              ENNReal.ofReal (C * s⁻¹ * Real.sqrt delta1))
    := SubdiffusiveProcess.Frozen.Section4.ellipticity_bound

end Paper
