module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.AnnealedProbeSum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.AnnealedContrastDecay
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.ContrastIndexBridge

@[expose] public section

/-!
# The annealed finite-probe sum decays algebraically

This is the annealed half of the quenched estimate, in exactly the shape the
`L^p` assembly consumes.  Three proved results are chained:

* `integral_finiteProbeSum_le` — the annealed probe sum on the centered cube of
  scale `k` is at most `3 d^2 (contrast(k) - 1)`;
* `thetaAtScale_normalizedCutoffLaw_eq_annealedContrast` — the development's
  contrast at cube scale `aCutoffNormalizationDepth d L + m` is the normalized
  law's Chapter 5 contrast index at scale `m`;
* `exists_annealed_contrast_decay_normalizedCutoffLaw` — that index decays to
  `1` algebraically above the annealed entry scale.

The result is unconditional: only the development's own `(P4)` moment record is
used, and no `DRAFT_SORRY` conclusion appears anywhere in the chain.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-- **The annealed decay of the finite probe sum.**

There is an entry scale `k₀` and an exponent `alpha > 0` such that on the
centered cube of scale `k₀ + n` the annealed finite probe sum is at most
`3 d^2 3^(-alpha n)`. -/
theorem exists_annealed_finiteProbeSum_decay [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) :
    ∃ (k₀ : ℕ) (alpha : ℝ), 0 < alpha ∧
      ∀ n : ℕ,
        (∫ omega, finiteProbeSum M L (ahom M L)
            (originCube d ((k₀ + n : ℕ) : ℤ)) omega ∂M.P.toMeasure) ≤
          3 * (d : ℝ) ^ 2 * Real.rpow (3 : ℝ) (-alpha * (n : ℝ)) := by
  obtain ⟨C, alpha, _hC, halpha, hdecay⟩ :=
    exists_annealed_contrast_decay_normalizedCutoffLaw M L
  set e : ℕ := Ch05.annealedAlgebraicEntryScale (normalizedCutoffLaw M L)
    (normalizedCutoffLaw_quantitativeCoarseGrainedEllipticity M L) C with he
  refine ⟨aCutoffNormalizationDepth d L + e, alpha, halpha, ?_⟩
  intro n
  have hindex := thetaAtScale_normalizedCutoffLaw_eq_annealedContrast M L (e + n)
  have hdec := hdecay n
  rw [hindex] at hdec
  have hassoc : aCutoffNormalizationDepth d L + (e + n) =
      aCutoffNormalizationDepth d L + e + n := by omega
  rw [hassoc] at hdec
  have hcontrast :
      abarScalarReadout M L (aCutoffNormalizationDepth d L + e + n) *
          oneStepAnnealedDualReadout M L
            (aCutoffNormalizationDepth d L + e + n) - 1 ≤
        Real.rpow (3 : ℝ) (-alpha * (n : ℝ)) := by linarith
  have hbase := integral_finiteProbeSum_le M L (aCutoffNormalizationDepth d L + e + n)
  refine hbase.trans ?_
  refine mul_le_mul_of_nonneg_left hcontrast ?_
  positivity

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
