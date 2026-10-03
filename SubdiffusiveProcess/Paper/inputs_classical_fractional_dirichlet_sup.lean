module

public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Paper.inputs_classical_fractional_sobolev_embedding
public import SubdiffusiveProcess.Paper.inputs_classical_e4_h1_finite
public import SubdiffusiveProcess.FractionalSup.Final

@[expose] public section




set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology

namespace Paper

/-- Fractional Sobolev coercivity controls the Dirichlet supremum by the source
bound and the supremum of the boundary datum, uniformly over coefficients. -/
theorem inputs_classical_fractional_dirichlet_sup
    (d : ℕ) (hd : 2 ≤ d) (s : Set.Ioo (0 : ℝ) 1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (K : ℝ), 0 < K →
        (∀ v : killedSobolevGraph (centeredCube z r hr),
          cubeFractionalSqNorm hd z r hr s
              (v : SobolevData (centeredCube z r hr)).1 ≤
            K * sobolevCoefficientForm a
              (v : SobolevData (centeredCube z r hr))
              (v : SobolevData (centeredCube z r hr))) →
        ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
          AEMeasurable F (volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d)), |F x| ≤ Kf) →
          ∀ (phi : SpatialCoordinates d → ℝ) (Bphi : ℝ), Continuous phi →
            (∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)), |phi x| ≤ Bphi) →
            ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
              ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
                  phi →
              SolvesDirichlet a F b u →
              ∀ (U : SpatialCoordinates d → ℝ), Continuous U →
                ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                  =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
                    U →
                ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
                  |U x| ≤ Bphi + C * K * Kf := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨CS, hCS, hleaf⟩ := inputs_classical_fractional_sobolev_embedding d hd s z r hr
  have hp2 := SubdiffusiveProcess.FractionalSup.critExp_gt_two hd s.2.1 s.2.2
  refine ⟨CS * (r ^ d) ^ ((SubdiffusiveProcess.FractionalSup.critExp d s - 2) /
      SubdiffusiveProcess.FractionalSup.critExp d s) *
    (2 : ℝ) ^ ((SubdiffusiveProcess.FractionalSup.critExp d s - 1) /
      (SubdiffusiveProcess.FractionalSup.critExp d s - 2)), by positivity, ?_⟩
  intro a K hK hcoer F Kf hKf hFm hFb phi Bphi _hphic hphib b u hb hsol U hU hu x hx
  exact SubdiffusiveProcess.FractionalSup.fractionalSup_bound hd s z r hr hCS
    (fun v hv => hleaf v hv)
    (fun Ψ hΨ => inputs_classical_e4_h1_finite d hd s z r hr
      ⟨Ψ, killedSobolevGraph_le_weakSobolevGraph hΨ⟩)
    a hK hcoer F hKf hFm hFb phi hphib b u hb hsol U hU hu x hx

end Paper
