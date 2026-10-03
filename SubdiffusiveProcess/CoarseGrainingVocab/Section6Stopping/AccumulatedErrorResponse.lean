module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.ResponseObservableMeasurability
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Action
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Discharge

@[expose] public section

/-!
# The response supremum inside the accumulated error

The frozen accumulated-error definition uses a real `sSup` over unit probe
directions.  This file identifies it with the `toReal` readout of the existing
measurable `paperScalarProbeMaxOn` carrier.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- The literal real unit-sphere response supremum is the real readout of the
public ENNReal sphere maximum. -/
theorem sSup_section6Response_unitSphere_eq_paperScalarProbeMaxOn_toReal
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (cubeScale cutoff : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d) :
    sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
        t = section6Response M cubeScale cutoff omega z e} =
      (paperScalarProbeMaxOn
        (Ch02.cubeDomain (originCube d (cubeScale : ℤ)))
        (aCutoffCoeffOnData M cutoff (translatePotentialSample z omega)
          (Ch02.cubeDomain (originCube d (cubeScale : ℤ)))).toCoeffOn
        (ahom M cutoff)).toReal := by
  letI : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)⟩
  let U := Ch02.cubeDomain (originCube d (cubeScale : ℤ))
  let omega' := translatePotentialSample z omega
  let a := (aCutoffCoeffOnData M cutoff omega' U).toCoeffOn
  let alpha := ahom M cutoff
  let Pmax := paperScalarProbeMaxOn U a alpha
  let values : Set ℝ := {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
    t = section6Response M cubeScale cutoff omega z e}
  let R := randomNormalizedResponseMatrix M cutoff U (fun _ => alpha) omega'
  have hPmax : Pmax = ENNReal.ofReal (Ch02.matrixOperatorNorm R) := by
    exact paperScalarProbeMaxOn_eq_ofReal_matrixOperatorNorm U a alpha R
      (randomNormalizedResponseMatrix_posSemidef M cutoff U (fun _ => alpha) omega')
      (randomNormalizedResponseMatrix_quadratic M cutoff U (fun _ => alpha) omega')
  have hPmax_ne : Pmax ≠ ∞ := by rw [hPmax]; exact ENNReal.ofReal_ne_top
  have hbdd : BddAbove values := by
    simpa only [values] using
      bddAbove_section6Response_unitSphere M cubeScale cutoff omega z
  have hresp_nonneg : ∀ e : Vec d,
      0 ≤ section6Response M cubeScale cutoff omega z e := by
    intro e
    unfold section6Response paperScalarProbe J
    exact Ch02.responseJ_nonneg _ _ _ _
  have hsphere : ∃ e : Vec d, vecNormSq e = 1 := by
    exact ⟨(Classical.arbitrary (ScalarProbeUnitSphere d)).1,
      (Classical.arbitrary (ScalarProbeUnitSphere d)).2⟩
  have hsup_nonneg : 0 ≤ sSup values := by
    obtain ⟨e, he⟩ := hsphere
    exact (hresp_nonneg e).trans (le_csSup hbdd ⟨e, he, rfl⟩)
  apply le_antisymm
  · apply csSup_le
    · obtain ⟨e, he⟩ := hsphere
      exact ⟨section6Response M cubeScale cutoff omega z e, e, he, rfl⟩
    rintro t ⟨e, he, rfl⟩
    have hprobe : ENNReal.ofReal (section6Response M cubeScale cutoff omega z e) ≤
        Pmax := by
      unfold Pmax paperScalarProbeMaxOn
      exact le_iSup_of_le ⟨e, he⟩ (le_refl _)
    exact (ENNReal.ofReal_le_iff_le_toReal hPmax_ne).mp hprobe
  · have hENN : Pmax ≤ ENNReal.ofReal (sSup values) := by
      unfold Pmax paperScalarProbeMaxOn
      refine iSup_le fun e => ?_
      apply ENNReal.ofReal_le_ofReal
      exact le_csSup hbdd ⟨e.1, e.2, rfl⟩
    have hreal := (ENNReal.toReal_le_toReal hPmax_ne ENNReal.ofReal_ne_top).2 hENN
    simpa [ENNReal.toReal_ofReal hsup_nonneg] using hreal

/-- Consequently the literal real response supremum is measurable in the
sample, for every fixed cube, cutoff, and centre. -/
theorem measurable_sSup_section6Response_unitSphere {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (cubeScale cutoff : ℕ) (z : Vec d) :
    Measurable (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
      sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
        t = section6Response M cubeScale cutoff omega z e}) := by
  let U := Ch02.cubeDomain (originCube d (cubeScale : ℤ))
  have hmax : Measurable (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
      paperScalarProbeMaxOn U
        (aCutoffCoeffOnData M cutoff omega U).toCoeffOn (ahom M cutoff)) :=
    measurable_paperScalarProbeMaxOn_cutoff_randomNormalization M cutoff U
      measurable_const
  have hcomp := ENNReal.measurable_toReal.comp
    (hmax.comp
      (Section6Covariance.measurable_translatePotentialSample z))
  convert hcomp using 1
  funext omega
  rw [sSup_section6Response_unitSphere_eq_paperScalarProbeMaxOn_toReal]
  rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
