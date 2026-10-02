import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Sobolev.ContinuousNativeRepresentative
import Homogenization.Geometry.ConvexDomain
import SubdiffusiveProcess.Paper.candidate_holder_harmonic_extension
import SubdiffusiveProcess.Paper.inputs_classical_elliptic_boundary_continuity_cube




open MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open scoped ContDiff ENNReal NNReal

noncomputable section
namespace Paper

/-- A smooth positive cutoff minimizer has a continuous representative with the prescribed trace and no greater energy than the boundary datum. -/
theorem aux_goodext_cutoff_trace_response_minimizer_control
    {d : ℕ} (hd : 2 ≤ d) {Ω : Opens (SpatialCoordinates d)}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hcube : Ω = centeredCube z r hr)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph Ω) u‖)
    (hΩ : Homogenization.IsOpenBoundedConvexDomain
      (Ω : Set (SpatialCoordinates d)))
    (a : PositiveCoefficient Ω) (b : weakSobolevGraph Ω)
    (A bRep : SpatialCoordinates d → ℝ)
    (hA : ContDiff ℝ ∞ A)
    (haA : a.val =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] A)
    (hApos : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ closure (Ω : Set (SpatialCoordinates d)),
      c ≤ A x)
    (hbRep : ContinuousOn bRep (closure (Ω : Set (SpatialCoordinates d))))
    (hb : ((b : SobolevData Ω).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] bRep) :
    ∃ V : SpatialCoordinates d → ℝ,
      ContinuousOn V (closure (Ω : Set (SpatialCoordinates d))) ∧
      (((dirichletMinimizer (killedResponseSpace hP) a b).val :
        SobolevData Ω).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] V ∧
      (∀ x ∈ frontier (Ω : Set (SpatialCoordinates d)), V x = bRep x) ∧
      sobolevCoefficientForm a (dirichletMinimizer (killedResponseSpace hP) a b).val
        (dirichletMinimizer (killedResponseSpace hP) a b).val ≤ sobolevCoefficientForm a b.val b.val := by
  obtain ⟨V, hVcont, hVae, hVtrace⟩ :=
    (haveI : NeZero d := ⟨by omega⟩
     inputs_classical_elliptic_boundary_continuity_cube hd z r hr hcube hP a b A bRep hA.continuous haA hApos hbRep hb)
  have hgap := dirichletResponse_energy_gap (killedResponseSpace hP) a b 0
  have hnonneg := sobolevCoefficientForm_nonneg a
    (b.val + (0 : (killedResponseSpace hP).space).val -
      (dirichletMinimizer (killedResponseSpace hP) a b).val)
  have henergy : sobolevCoefficientForm a b.val b.val =
      dirichletResponse (killedResponseSpace hP) a b +
        sobolevCoefficientForm a
          (b.val + (0 : (killedResponseSpace hP).space).val -
            (dirichletMinimizer (killedResponseSpace hP) a b).val)
          (b.val + (0 : (killedResponseSpace hP).space).val -
            (dirichletMinimizer (killedResponseSpace hP) a b).val) := by
    simpa only [dirichletResponse, Submodule.coe_zero, add_zero] using hgap
  refine ⟨V, hVcont, hVae, hVtrace, ?_⟩
  rw [dirichletResponse] at henergy
  linarith only [henergy, hnonneg]

/-- A finite cutoff minimizes among extensions of its actual Hölder trace, with the controlled extension cost. -/
theorem goodext_cutoff_trace_response
    {d : ℕ} (hd : 2 ≤ d)
    (Sob : Lane4.SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (Cext : ℝ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (hΩ : Homogenization.IsOpenBoundedConvexDomain
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (a : PositiveCoefficient (centeredCube z r hr))
    (A U : SpatialCoordinates d → ℝ)
    (hA : ContDiff ℝ ∞ A)
    (haA : a.val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] A)
    (hApos : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), c ≤ A x)
    (hU : Lane4.IsHolderOn beta
      (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) U)
    (hResponseEstimate : ∀ (b : weakSobolevGraph (centeredCube z r hr))
      (G : SpatialCoordinates d → ℝ),
      ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
      Lane4.IsHolderOn beta
        (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
      ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G →
      dirichletResponse (killedResponseSpace hP) a b ≤
        Cext * r ^ ((d : ℝ) - 2) *
          (r ^ beta * Lane4.holderSeminorm beta
            (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2) :
    ∃ (b : weakSobolevGraph (centeredCube z r hr)) (V : SpatialCoordinates d → ℝ),
      ContinuousOn V (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      (((dirichletMinimizer (killedResponseSpace hP) a b).val :
        SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] V ∧
      (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), V x = U x) ∧
      sobolevCoefficientForm a
        (dirichletMinimizer (killedResponseSpace hP) a b).val
        (dirichletMinimizer (killedResponseSpace hP) a b).val ≤
        sobolevCoefficientForm a b.val b.val ∧
      sobolevCoefficientForm a
        (dirichletMinimizer (killedResponseSpace hP) a b).val
        (dirichletMinimizer (killedResponseSpace hP) a b).val ≤
        Cext * r ^ ((d : ℝ) - 2) *
          (r ^ beta * Lane4.holderSeminorm beta
            (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) U) ^ 2 := by
  obtain ⟨b, B, hBcont, hBae, htrace⟩ :=
    aux_candidate_holder_harmonic_extension_datum hd Sob beta hbeta z r hr U hU
  have hBholder : Lane4.IsHolderOn beta
      (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) B :=
    (SubdiffusiveProcess.isHolderOn_congr htrace).2 hU
  obtain ⟨V, hVcont, hVae, hVtrace, hVenergy⟩ :=
    aux_goodext_cutoff_trace_response_minimizer_control hd z r hr rfl hP hΩ a b A B hA haA hApos
      hBcont.continuousOn hBae
  have hresponse := hResponseEstimate b B hBcont.continuousOn hBholder hBae
  have hsemi : Lane4.holderSeminorm beta
      (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) B =
      Lane4.holderSeminorm beta
        (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) U := by
    unfold Lane4.holderSeminorm
    rw [SubdiffusiveProcess.holderRatioSet_congr htrace]
  refine ⟨b, V, hVcont, hVae, ?_, hVenergy, ?_⟩
  · intro x hx
    exact (hVtrace x hx).trans (htrace x hx)
  · change dirichletResponse (killedResponseSpace hP) a b ≤ _
    rw [← hsemi]
    exact hresponse

end Paper
end
