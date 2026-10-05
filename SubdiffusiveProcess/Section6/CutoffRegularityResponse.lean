module

public import SubdiffusiveProcess.Vocab.NormalizedDefect
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ResponseMoment

@[expose] public section

set_option autoImplicit false
open Homogenization Homogenization.Book MeasureTheory
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal
noncomputable section

/-- Response estimates uniformly in the cutoff.
Source: `l.cutoff.regularity.response`.
`normalizedDefect` uses the equivalent loadings
`ahom^(-1/2) e`, `ahom^(1/2) e` from the homogeneity identity.
The observation cube has scale `n`; the coefficient and normalization have
scale `min n L`. -/
theorem SubdiffusiveProcess.Section6.cutoff_regularity_response {d : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ M : GMCModel d, ∀ p : ℝ,
      1 ≤ p → p ≤ C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
      ∀ L n : ℕ,
        paperENNRealLpNorm M.P.toMeasure p
          (normalizedDefect M (min n L) (Ch02.cubeDomain (originCube d (n : ℤ)))) ≤
        ENNReal.ofReal (C * p * Real.log (2 + p) * M.delta ^ 2)
:= by
  obtain ⟨_, C, _, hC, h⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.exists_cutoffNormalizedResponse_moment_bound d
  exact ⟨C, hC, fun M p hp hp' L n => h M p hp hp' L n⟩
