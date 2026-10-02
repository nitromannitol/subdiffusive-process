import SubdiffusiveProcess.Analysis.CompactPotentialC1Norm
import SubdiffusiveProcess.Analysis.CompactGradientLipschitz
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellSeries

open MeasureTheory TopologicalSpace
noncomputable section
namespace SubdiffusiveProcess

theorem shellC11Summable_compact_observables {d : ℕ}
    (f : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hf : SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellC11Summable f)
    (K : Compacts (SpatialCoordinates d)) :
    Summable (fun n => compactPotentialC1Norm K
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n))) ∧
    Summable (fun n => compactGradientLipschitzObservable K (f n)) := by
  obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall (0 : SpatialCoordinates d)
  obtain ⟨u, v, w, hb⟩ := hf R
  have hC1 : ∀ n, compactPotentialC1Norm K
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (f n)) ≤ u n + v n := by
    intro n
    unfold compactPotentialC1Norm
    apply add_le_add
    · apply (ContinuousMap.norm_le _ (hb.u_nonneg n)).2
      intro x
      simpa only [ContinuousMap.coe_mk,
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor_apply, Real.norm_eq_abs] using
        hb.value_le n x.1 (hR x.2)
    · apply (ContinuousMap.norm_le _ (hb.v_nonneg n)).2
      intro x
      simpa only [ContinuousMap.coe_mk,
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor_deriv] using
        hb.deriv_le n x.1 (hR x.2)
  have hLip : ∀ n, compactGradientLipschitzObservable K (f n) ≤ w n := by
    intro n
    apply Real.sSup_le _ (hb.w_nonneg n)
    rintro a ⟨x, y, hxy, rfl⟩
    have hnorm : 0 < ‖x.1 - y.1‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hxy (Subtype.ext h)))
    exact (div_le_iff₀ hnorm).2 (hb.deriv_lipschitz n x.1 (hR x.2) y.1 (hR y.2))
  constructor
  · apply Summable.of_nonneg_of_le _ hC1 (hb.u_summable.add hb.v_summable)
    intro n
    unfold compactPotentialC1Norm
    positivity
  · apply Summable.of_nonneg_of_le _ hLip hb.w_summable
    intro n
    apply Real.sSup_nonneg
    rintro a ⟨x, y, hxy, rfl⟩
    exact div_nonneg (norm_nonneg _) (norm_nonneg _)

end SubdiffusiveProcess
