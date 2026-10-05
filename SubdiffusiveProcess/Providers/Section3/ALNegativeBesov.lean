module

public import SubdiffusiveProcess.CoarseGrainingVocab.NegativeBesovScaleSum

@[expose] public section

/-!
# Negative-Besov provider assembly

The forward estimate is assembled from the fresh-shell block moment, the
uniform descendant-block estimate, and the normalized exact-circ scale sum.
The inverse conclusion then follows with the same constant from whole-sequence
negation invariance.

this law-transport-before-recombination split mirrors
 and the final
assembly organization in `Stream/IncrementEstimates.lean`.
-/

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open scoped ENNReal

namespace SubdiffusiveProcess.Providers.Section3

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

private abbrev Sample (d : ℕ) := _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- Source Step 1 (`e.condy.moment.bound`), including the terminal fresh
shell.  The smallness premise is retained for the subsequent shell sum; the
single-block estimate itself uses only the GMC model assumptions. -/
theorem freshShell_block_moment {d : ℕ} :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (p : ℝ), 2 ≤ p →
        p * M.delta ^ 2 * Real.log (2 + p) ≤ c →
        ∀ (m r : ℕ) (R : Homogenization.TriadicCube d), r ≤ m →
          (r : ℤ) - 1 ≤ R.scale → R.scale ≤ (m : ℤ) →
          let gap : ℝ := ((R.scale - ((r : ℤ) - 1) : ℤ) : ℝ)
          paperLpNorm M.P.toMeasure p (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦
              ∫ x, cutoffFreshShellTerm M m r omega x
                ∂normalizedCubeMeasure R) ≤
            ENNReal.ofReal
              (C * M.delta * Real.sqrt p *
                (Real.rpow 3 (-((d : ℝ) / 2) * gap) +
                  min
                    (p * Real.rpow 3
                      (-(d : ℝ) * (1 - p⁻¹) * gap)) 1) *
                Real.exp (C * p * M.delta ^ 2 * ((m + 1 - r : ℕ) : ℝ))) := by
  refine ⟨negativeBesovFreshShellFinalConst d, 1,
    negativeBesovFreshShellFinalConst_pos d, by norm_num, ?_⟩
  intro M p hp hsmall m r R hrm hrR hRm
  exact negativeBesov_freshShell_block_paperLpNorm_source M hp m r R hrm hrR hRm

/-- Source Step 2 (`e.am.Besov.onecube`), uniformly over all exact-circ
descendant blocks. -/
theorem cutoffRatio_oneCube_moment {d : ℕ} :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (p : ℝ), 2 ≤ p →
        p * M.delta ^ 2 * Real.log (2 + p) ≤ c →
        ∀ (m : ℕ) (n : ℤ), -1 ≤ n → n < (m : ℤ) →
          ∀ (depth : ℕ) (R : Homogenization.TriadicCube d)
            (hR : R ∈ descendantsAtDepth (originCube d (m : ℤ)) depth),
            paperLpNorm M.P.toMeasure p (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦
                exactCircBlockMean R (cutoffRatioMinusOne M m n omega)
                  ((cutoffRatioExactCircIntegrable M m n omega).block depth R hR)) ≤
              ENNReal.ofReal
                (C * M.delta * Real.sqrt p * Real.log p * (1 + depth : ℕ) *
                  Real.exp (C * p * M.delta ^ 2 * (depth : ℝ))) := by
  refine ⟨negativeBesovOneCubeConst d, negativeBesovOneCubeSmallConst d,
    negativeBesovOneCubeConst_pos d, negativeBesovOneCubeSmallConst_pos d, ?_⟩
  intro M p hp hsmall m n hn hnm depth R hR
  exact negativeBesov_cutoffRatio_oneCube_moment
    M hp hsmall m n hn hnm depth R hR

/-- Source Step 3 (`e.aL.Besov.sumscales`), summing the exact-circ diagonal
after the normalized one-cube estimate. -/
theorem forward_a_l_negative_besov {d : ℕ} :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s p : ℝ),
        0 < s → s ≤ 1 → 2 ≤ p →
        C * p * M.delta ^ 2 ≤ s →
        p * M.delta ^ 2 * Real.log (2 + p) ≤ c →
        ∀ (m : ℕ) (n : ℤ), -1 ≤ n → n < (m : ℤ) →
          ENNReal.ofReal (Real.rpow 3 (-s * (m : ℝ))) *
              paperENNRealLpNorm M.P.toMeasure p
                (cutoffRatioNegativeBesov M m n s p) ≤
            ENNReal.ofReal (C * s⁻¹ * M.delta * Real.sqrt p * Real.log p) := by
  exact negativeBesov_cutoffRatio_scaleSum_moment

/-- The exact two-sided conclusion follows from its forward half.  The
inverse half is transported by `e.inverse.symmetry.in.law`, proved on the
actual `ENNReal` moment carrier in `NegativeBesovSupport`. -/
theorem a_l_negative_besov_of_forward {d : ℕ}
    (hforward :
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s p : ℝ),
          0 < s → s ≤ 1 → 2 ≤ p →
          C * p * M.delta ^ 2 ≤ s →
          p * M.delta ^ 2 * Real.log (2 + p) ≤ c →
          ∀ (m : ℕ) (n : ℤ), -1 ≤ n → n < (m : ℤ) →
            ENNReal.ofReal (Real.rpow 3 (-s * (m : ℝ))) *
                paperENNRealLpNorm M.P.toMeasure p
                  (cutoffRatioNegativeBesov M m n s p) ≤
              ENNReal.ofReal
                (C * s⁻¹ * M.delta * Real.sqrt p * Real.log p)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s p : ℝ),
        0 < s → s ≤ 1 → 2 ≤ p →
        C * p * M.delta ^ 2 ≤ s →
        p * M.delta ^ 2 * Real.log (2 + p) ≤ c →
        ∀ (m : ℕ) (n : ℤ), -1 ≤ n → n < (m : ℤ) →
          ENNReal.ofReal (Real.rpow 3 (-s * (m : ℝ))) *
              paperENNRealLpNorm M.P.toMeasure p
                (cutoffRatioNegativeBesov M m n s p) ≤
            ENNReal.ofReal (C * s⁻¹ * M.delta * Real.sqrt p * Real.log p) ∧
          ENNReal.ofReal (Real.rpow 3 (-s * (m : ℝ))) *
              paperENNRealLpNorm M.P.toMeasure p
                (inverseCutoffRatioNegativeBesov M m n s p) ≤
            ENNReal.ofReal (C * s⁻¹ * M.delta * Real.sqrt p * Real.log p) := by
  obtain ⟨C, c, hC, hc, hbound⟩ := hforward
  refine ⟨C, c, hC, hc, ?_⟩
  intro M s p hs hs1 hp hscale hsmall m n hn hnm
  have hf := hbound M s p hs hs1 hp hscale hsmall m n hn hnm
  refine ⟨hf, ?_⟩
  rw [paperENNRealLpNorm_inverseCutoffRatioNegativeBesov_eq_forward M m n s p hn]
  exact hf

/-- Exact provider for the two-sided negative-Besov anchor. -/
theorem a_l_negative_besov {d : ℕ} :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s p : ℝ),
        0 < s → s ≤ 1 → 2 ≤ p →
        C * p * M.delta ^ 2 ≤ s →
        p * M.delta ^ 2 * Real.log (2 + p) ≤ c →
        ∀ (m : ℕ) (n : ℤ), -1 ≤ n → n < (m : ℤ) →
          ENNReal.ofReal (Real.rpow 3 (-s * (m : ℝ))) *
              paperENNRealLpNorm M.P.toMeasure p
                (cutoffRatioNegativeBesov M m n s p) ≤
            ENNReal.ofReal (C * s⁻¹ * M.delta * Real.sqrt p * Real.log p) ∧
          ENNReal.ofReal (Real.rpow 3 (-s * (m : ℝ))) *
              paperENNRealLpNorm M.P.toMeasure p
                (inverseCutoffRatioNegativeBesov M m n s p) ≤
            ENNReal.ofReal (C * s⁻¹ * M.delta * Real.sqrt p * Real.log p) :=
  a_l_negative_besov_of_forward forward_a_l_negative_besov

end

end SubdiffusiveProcess.Providers.Section3
