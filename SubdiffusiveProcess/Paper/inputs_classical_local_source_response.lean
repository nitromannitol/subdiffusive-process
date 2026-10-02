import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Sobolev.LocalEnergy
import SubdiffusiveProcess.LocalSource.Comparison
import SubdiffusiveProcess.Lane2.CellDirichlet
import SubdiffusiveProcess.Lane1.ChaosBasic



set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped NNReal ENNReal
namespace Paper

/-- Classical restriction and harmonic comparison bound local sourced energy by its trace response. -/
theorem inputs_classical_local_source_response {d : ℕ} (hd : 1 ≤ d)
    (Ω : Opens (SpatialCoordinates d)) [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (a : PositiveCoefficient Ω) (u : weakSobolevGraph Ω)
    (F : SpatialCoordinates d → ℝ) (Kf Ks : ℝ) (hKf : 0 ≤ Kf) (hKs : 0 ≤ Ks)
    (hFm : AEMeasurable F (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),|F x| ≤ Kf)
    (hweak : ∀ psi : killedSobolevGraph Ω,
      sobolevCoefficientForm a (u : SobolevData Ω) (psi : SobolevData Ω) =
        ∫ x in (Ω : Set (SpatialCoordinates d)),F x*(psi : SobolevData Ω).1 x)
    (U : SpatialCoordinates d → ℝ) (hU : Continuous U)
    (hu : ((u : SobolevData Ω).1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] U)
    (hUb : ∀ x ∈ closure (Ω : Set (SpatialCoordinates d)),|U x| ≤ Ks)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hsub : centeredCube z r hr ≤ Ω)
    (aq : PositiveCoefficient (centeredCube z r hr))
    (haq : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), aq.val x = a.val x)
    (hP : ∃ K : ℝ≥0,∀ v : killedSobolevGraph (centeredCube z r hr),
      ‖(v : SobolevData (centeredCube z r hr)).1‖ ≤
        K*‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) v‖) :
    ∃ v : weakSobolevGraph (centeredCube z r hr),
      (((v : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U) ∧
      localGradientEnergy a (centeredCube z r hr).isOpen.measurableSet (sobolevGradient (u : SobolevData Ω)) ≤
        dirichletResponse (killedResponseSpace hP) aq v + 2*Kf*Ks*r^d := by
  haveI : NeZero d := ⟨by omega⟩
  have hvol : volume (centeredCube z r hr : Set (SpatialCoordinates d)) < ⊤ := by
    rw [centeredCube_coe_eq_ball]; exact measure_ball_lt_top
  obtain ⟨v, hv, hE⟩ := localSource_comparison
    (lane2_isOpenBoundedConvexDomain_centeredCube z hr) hvol a u F Kf Ks hKf hKs hFb hweak U hu
    hUb hsub aq haq hP
  refine ⟨v, hv, ?_⟩
  rw [localSource_volume_real_centeredCube z hr] at hE
  exact hE

end Paper
