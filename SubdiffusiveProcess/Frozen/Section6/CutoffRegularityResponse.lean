module

public import SubdiffusiveProcess.Frozen.Vocab.NormalizedDefect
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ResponseMoment

@[expose] public section

set_option autoImplicit false
open Homogenization Homogenization.Book MeasureTheory
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal
noncomputable section




theorem SubdiffusiveProcess.Frozen.Section6.cutoff_regularity_response {d : ℕ} :
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
