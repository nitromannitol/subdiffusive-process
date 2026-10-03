module

public import SubdiffusiveProcess.Sobolev.DiagonalDefect
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Polarization.Responses
public import SubdiffusiveProcess.Lane1.ChaosBasic

@[expose] public section



set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace Paper

/-- Relative errors on a finite polarization bank control its maximal diagonal defect. -/
theorem inputs_classical_affine_response_polarization (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (hD : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
          ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
            K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
        (hN : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph (centeredCube z r hr),
          ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
            K * ‖subspaceGradient (meanZeroSobolevGraph (centeredCube z r hr)) u‖)
        (a b : PositiveCoefficient (centeredCube z r hr)) (eta : ℝ), 0 ≤ eta →
      let vol : ℝ := volume.real (centeredCube z r hr : Set (SpatialCoordinates d));
      let dirs : Fin d ⊕ (Fin d × Fin d) → SpatialCoordinates d :=
        Sum.elim (fun i => Pi.single i 1)
          (fun ij => Pi.single ij.1 1 + Pi.single ij.2 1);
      let response : PositiveCoefficient (centeredCube z r hr) →
          Bool → SpatialCoordinates d → ℝ := fun q inverse e =>
        if inverse then affineInverseNeumannResponse hN q e
        else affineDirichletResponse (centeredCube_isBounded z hr) hD q e;
      let defect : PositiveCoefficient (centeredCube z r hr) → ℝ := fun q =>
        sSup {v : ℝ | ∃ e : SpatialCoordinates d, (∑ i : Fin d, (e i) ^ 2) = 1 ∧
          v = (response q false e + response q true e) / (2 * vol) - 1};
      (∀ i inverse, |response a inverse (dirs i) - response b inverse (dirs i)| ≤
        eta * (vol + response b inverse (dirs i))) →
      |defect a - defect b| ≤ C * eta * (1 + defect b) := by
  obtain ⟨C, hC, hcore⟩ := SubdiffusiveProcess.Polarization.polarization_defect hd
  refine ⟨C, hC, ?_⟩
  intro z r hr hD hN a b eta heta vol dirs response defect hrel
  have hvolpos : 0 < vol := by
    show 0 < volume.real (centeredCube z r hr : Set (SpatialCoordinates d))
    rw [centeredCube_coe_eq_ball, Measure.real, Real.volume_pi_ball z (by positivity),
      ENNReal.toReal_ofReal (by positivity)]
    positivity
  have hquad : ∀ q : PositiveCoefficient (centeredCube z r hr),
      SubdiffusiveProcess.Polarization.IsQuadPair (response q) := by
    intro q x
    cases x
    · obtain ⟨G, hG, hGq⟩ := affineDirichletResponse_isQuad (centeredCube_isBounded z hr) hD q
      exact ⟨G, hG, fun p => hGq p⟩
    · obtain ⟨G, hG, hGq⟩ := affineInverseNeumannResponse_isQuad hN q
      exact ⟨G, hG, fun p => hGq p⟩
  have hnn : ∀ (x : Bool) (p : SpatialCoordinates d), 0 ≤ response b x p := by
    intro x p
    cases x
    · exact dirichletResponse_nonneg _ _ _
    · exact inverseResponse_nonneg _ _ _
  have hpd : ∀ e : SpatialCoordinates d, ∑ i : Fin d, e i ^ 2 = 1 →
      2 * vol ≤ response b false e + response b true e := by
    intro e he
    have := affineResponses_sum_ge (centeredCube_isBounded z hr) hvolpos.ne' hD hN b e
    rw [he, mul_one] at this
    exact this
  exact hcore vol hvolpos (response a) (response b) eta heta (hquad a) (hquad b) hnn hpd
    (fun x => ⟨fun i => hrel (Sum.inl i) x, fun i j => hrel (Sum.inr (i, j)) x⟩)

end Paper
