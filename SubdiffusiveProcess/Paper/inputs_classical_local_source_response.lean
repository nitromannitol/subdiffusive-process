module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.LocalEnergy
public import SubdiffusiveProcess.LocalSource.Comparison
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet
public import SubdiffusiveProcess.MultiplicativeChaos.ChaosBasic

@[expose] public section

/-! Local variational comparison with the homogeneous Dirichlet minimizer.
This is a statement for arbitrary uniformly elliptic scalar coefficients and bounded sources;
it contains no multiscale or stochastic estimate. PROVED: the Dirichlet principle (orthogonality
of the harmonic minimizer), the weak maximum principle for the minimizer, and testing the equation
with the zero extension of the zero-trace difference; see `SubdiffusiveProcess.LocalSource.Harmonic`, `SubdiffusiveProcess.LocalSource.MaxPrinciple`, `SubdiffusiveProcess.LocalSource.Comparison`. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped NNReal ENNReal
namespace SubdiffusiveProcess.Paper

/-- Classical restriction and harmonic comparison bound local sourced energy by its trace response. -/
theorem inputs_classical_local_source_response {d : ℕ} (hd : 1 ≤ d)
    (Ω : Opens (SpatialCoordinates d)) [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (a : PositiveCoefficient Ω) (u : weakSobolevGraph Ω)
    (F : SpatialCoordinates d → ℝ) (Kf Ks : ℝ) (hKf : 0 ≤ Kf) (hKs : 0 ≤ Ks)
    (_hFm : AEMeasurable F (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),|F x| ≤ Kf)
    (hweak : ∀ psi : killedSobolevGraph Ω,
      sobolevCoefficientForm a (u : SobolevData Ω) (psi : SobolevData Ω) =
        ∫ x in (Ω : Set (SpatialCoordinates d)),F x*(psi : SobolevData Ω).1 x)
    (U : SpatialCoordinates d → ℝ) (_hU : Continuous U)
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
  have : NeZero d := ⟨by omega⟩
  have hvol : volume (centeredCube z r hr : Set (SpatialCoordinates d)) < ⊤ := by
    rw [centeredCube_coe_eq_ball]; exact measure_ball_lt_top
  obtain ⟨v, hv, hE⟩ := localSource_comparison
    (isOpenBoundedConvexDomain_centeredCube z hr) hvol a u F Kf Ks hKf hKs hFb hweak U hu
    hUb hsub aq haq hP
  refine ⟨v, hv, ?_⟩
  rw [localSource_volume_real_centeredCube z hr] at hE
  exact hE

end SubdiffusiveProcess.Paper
