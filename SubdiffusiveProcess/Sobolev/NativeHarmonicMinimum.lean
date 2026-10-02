import SubdiffusiveProcess.Sobolev.NativeBoundaryMinimizer
import SubdiffusiveProcess.Lane2.CellDirichlet

/-! Native harmonic functions minimize energy in their prescribed trace class.
The coefficient is fixed; no random or limiting bounds are asserted. -/
open MeasureTheory Set TopologicalSpace Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
namespace SubdiffusiveProcess

/-- A native harmonic function has energy equal to the native boundary infimum. -/
theorem native_harmonic_energy_eq_infimum
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Q) (c : SpatialCoordinates d → ℝ)
    (hc : (fun x => a.val x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] c)
    (beta v : H1Function (Q : Set (SpatialCoordinates d)))
    (htrace : HasZeroTraceDifferenceOn (Q : Set (SpatialCoordinates d)) v beta)
    (hharm : IsWeaklyHarmonicOn c (Q : Set (SpatialCoordinates d)) v) :
    energy c (Q : Set (SpatialCoordinates d)) v =
      cellDirichletInfimum c (Q : Set (SpatialCoordinates d)) beta := by
  obtain ⟨C, hC⟩ := lane2_coeff_ae_bound a
  apply lane2_energy_isLeast (C := C) (Lp.aestronglyMeasurable a.val |>.congr hc)
  · filter_upwards [hC, hc] with x hCx hx
    simpa only [← hx] using hCx
  · filter_upwards [positiveCoefficient_ae_nonneg a, hc] with x hax hx
    simpa only [← hx] using hax
  · exact hharm
  · exact htrace

end SubdiffusiveProcess
