module

public import SubdiffusiveProcess.Geometry.TriadicFinitePartition

@[expose] public section

open MeasureTheory Set TopologicalSpace
noncomputable section
namespace SubdiffusiveProcess

/-- An actual adaptive partition covering a positive-volume cube has an active plane. -/
theorem triadicAdaptivePlanes_nonempty_of_ae_cover
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (I : Finset (Fin d)) (J : ℕ)
    (hcover : (⋃ t ∈ triadicAdaptiveLabels I J,
      (triadicAdaptiveCell z r hr J t : Set (SpatialCoordinates d)))
        =ᵐ[volume] (centeredCube z r hr : Set (SpatialCoordinates d))) :
    I.Nonempty := by
  classical
  by_contra hI
  have hIe : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
  have hlabels : triadicAdaptiveLabels I J = ∅ := by
    subst I
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    have ht' := (Finset.mem_filter.mp ht).2
    rcases t with ⟨j, k⟩ | k
    · simpa [triadicRetainedLabels, oddGridUnresolved] using ht'
    · simpa [oddGridUnresolved] using ht'
  simp only [hlabels, Finset.notMem_empty, iUnion_of_empty, iUnion_empty] at hcover
  have hmeasure := measure_congr hcover
  have hzero : volume (centeredCube z r hr : Set (SpatialCoordinates d)) = 0 := by
    simpa using hmeasure.symm
  have hpos := centeredCube_volume_pos z hr
  rw [measureReal_def, hzero, ENNReal.toReal_zero] at hpos
  exact (lt_irrefl 0) hpos

end SubdiffusiveProcess
