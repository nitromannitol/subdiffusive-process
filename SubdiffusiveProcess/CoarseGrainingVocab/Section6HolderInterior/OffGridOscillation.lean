module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.OffGridTransfer
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.OffGridWindows
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoConversion

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

/-- **The off-grid oscillation transfer.**  An off-grid window's oscillation is
controlled by that of any larger window containing it, at the dimension-only
volume ratio — the `normalizedL2On` analogue of
`Section6Holder.excess_truncatedCube_crossCentre_le`. -/
theorem normalizedL2On_sub_average_crossCentre_le
    {d : ℕ} {m j ell : ℤ} {x z : Vec d}
    (hx : x ∈ cube d m) (hz : z ∈ cube d m)
    (hjm : j - 1 ≤ m) (hellm : ell - 1 ≤ m)
    (hsub : truncatedCube d m j x ⊆ truncatedCube d m ell z)
    (u : H1Function (openCubeSet (originCube d m))) :
    normalizedL2On (truncatedCube d m j x)
        (fun p => u.toFun p - averageOn (truncatedCube d m j x) u.toFun) ≤
      Real.sqrt (((3 : ℝ) ^ (ell - j + 2)) ^ d) *
        normalizedL2On (truncatedCube d m ell z)
          (fun p => u.toFun p - averageOn (truncatedCube d m ell z) u.toFun) := by
  set W := truncatedCube d m j x with hWdef
  set Q := truncatedCube d m ell z with hQdef
  have hWm : MeasurableSet W := measurableSet_truncatedCube d m j x
  have hWpos : 0 < (volume W).toReal := volume_toReal_truncatedCube_pos x hx hjm
  have hWfin : volume W ≠ ⊤ := (volume_truncatedCube_lt_top d m j x).ne
  have huQ : MemLp u.toFun 2 (volume.restrict Q) :=
    u.memL2.mono_measure
      (Measure.restrict_mono (truncatedCube_subset_cube d m ell z) le_rfl)
  have huW : MemLp u.toFun 2 (volume.restrict W) :=
    u.memL2.mono_measure
      (Measure.restrict_mono (truncatedCube_subset_cube d m j x) le_rfl)
  -- the window's own mean minimizes: substitute the outer mean at no cost
  have hmean : normalizedL2On W (fun p => u.toFun p - averageOn W u.toFun) ≤
      normalizedL2On W (fun p => u.toFun p - averageOn Q u.toFun) := by
    apply Section6Iteration.normalizedL2On_sub_volumeAverage_le hWm hWpos hWfin
    · exact integrableOn_truncatedCube x huW
    · exact huW.integrable_sq
  -- restrict along the inclusion, paying the volume ratio
  have hQfin : volume Q ≠ ⊤ := (volume_truncatedCube_lt_top d m ell z).ne
  have : IsFiniteMeasure (volume.restrict Q) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hQfin⟩
  have hmemQ : MemLp (fun p => u.toFun p - averageOn Q u.toFun) 2
      (volume.restrict Q) := huQ.sub (memLp_const _)
  have hcross := Section6Holder.normalizedL2On_truncatedCube_crossCentre_le
    (f := fun p => u.toFun p - averageOn Q u.toFun)
    hx hz hjm hellm hsub hmemQ.integrable_sq
  exact hmean.trans hcross

/-- The transfer in the shape row 2 consumes: the off-grid base point's window
against a grid centre's window one scale larger. -/
theorem offGrid_oscillation_le_grid
    {d : ℕ} {m n : ℕ} {x z : Vec d}
    (hx : x ∈ cube d (m : ℤ)) (hz : z ∈ cube d (m : ℤ))
    (hnm : (n : ℤ) ≤ (m : ℤ))
    (hsub : truncatedCube d (m : ℤ) (n : ℤ) x ⊆
      truncatedCube d (m : ℤ) ((n : ℤ) + 1) z)
    (u : H1Function (openCubeSet (originCube d (m : ℤ)))) :
    normalizedL2On (truncatedCube d (m : ℤ) (n : ℤ) x)
        (fun p => u.toFun p -
          averageOn (truncatedCube d (m : ℤ) (n : ℤ) x) u.toFun) ≤
      Real.sqrt (((3 : ℝ) ^ (3 : ℤ)) ^ d) *
        normalizedL2On (truncatedCube d (m : ℤ) ((n : ℤ) + 1) z)
          (fun p => u.toFun p -
            averageOn (truncatedCube d (m : ℤ) ((n : ℤ) + 1) z) u.toFun) := by
  have hraw := normalizedL2On_sub_average_crossCentre_le
    (m := (m : ℤ)) (j := (n : ℤ)) (ell := (n : ℤ) + 1)
    hx hz (by omega) (by omega) hsub u
  have hexp : ((n : ℤ) + 1) - (n : ℤ) + 2 = (3 : ℤ) := by ring
  rwa [hexp] at hraw

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
