module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.AnnealedDualMeanDefect
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ResponseMoment
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.AccumulatedErrorResponse

@[expose] public section

/-!
# The literal cutoff response supremum

This module connects the real unit-sphere supremum appearing in the frozen
good-event and accumulated-error definitions to the normalized-defect carrier
controlled by the uniform cutoff response moment.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- The literal real response maximum with the manuscript cutoff `n ∧ L`. -/
def cutoffResponseSupremum {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (omega : Sample d) (z : Vec d) : ℝ :=
  sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
    t = section6Response M n (min n L) omega z e}

theorem measurable_cutoffResponseSupremum {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (z : Vec d) :
    Measurable (fun omega : Sample d => cutoffResponseSupremum M L n omega z) := by
  exact measurable_sSup_section6Response_unitSphere M n (min n L) z

theorem normalizedDefect_ne_top {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (omega : Sample d) :
    normalizedDefect M L U omega ≠ ∞ := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.aux_dedup_d203_normalizedDefect_ne_top (d := d) (M := M) (L := L) (U := U) (omega := omega)

/-- At the origin, the ENNReal readout of the literal supremum is exactly the
normalized defect on the scale-`n` cube with cutoff `n ∧ L`. -/
theorem ofReal_cutoffResponseSupremum_zero_eq_normalizedDefect {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (omega : Sample d) :
    ENNReal.ofReal (cutoffResponseSupremum M L n omega 0) =
      normalizedDefect M (min n L)
        (Ch02.cubeDomain (originCube d (n : ℤ))) omega := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  rw [cutoffResponseSupremum,
    sSup_section6Response_unitSphere_eq_paperScalarProbeMaxOn_toReal,
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.translatePotentialSample_zero]
  change ENNReal.ofReal
      ((normalizedDefect M (min n L)
        (Ch02.cubeDomain (originCube d (n : ℤ))) omega).toReal) = _
  exact ENNReal.ofReal_toReal
    (normalizedDefect_ne_top M (min n L)
      (Ch02.cubeDomain (originCube d (n : ℤ))) omega)

/-- Manuscript-shaped uniform moment bound for the literal cutoff response
supremum at the centered cube. -/
theorem exists_cutoffResponseSupremum_moment_bound (d : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (xi : ℝ),
        1 ≤ xi →
        xi ≤ C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
        ∀ L n : ℕ,
          paperENNRealLpNorm M.P.toMeasure xi
              (fun omega => ENNReal.ofReal
                (cutoffResponseSupremum M L n omega 0)) ≤
            ENNReal.ofReal (C * xi * Real.log (2 + xi) * M.delta ^ 2) := by
  obtain ⟨c, C, hc, hC, hmoment⟩ :=
    exists_cutoffNormalizedResponse_moment_bound d
  refine ⟨c, C, hc, hC, ?_⟩
  intro M xi hxi hxiMax L n
  simpa only [ofReal_cutoffResponseSupremum_zero_eq_normalizedDefect] using
    hmoment M xi hxi hxiMax L n

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
