import SubdiffusiveProcess.Paper.goodext_dirichlet_response_bound
import SubdiffusiveProcess.Sobolev.NormalizedBoundaryHolder
import SubdiffusiveProcess.Sobolev.GoodCellEnergyScaling
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
/-- The good-cell source Holder estimate directly bounds finite-coefficient
harmonic energy. No limiting boundary minimum is identified or assumed. -/
theorem density_finite_source_response
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (X : in_extension d hd I) (Sob : SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta : beta ∈ Ioo (1 / 2 : ℝ) 1) :
    ∃ Ce : ℝ, 0 < Ce ∧ ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ (alpha Cnorm se sf nu fsup upper : ℝ), beta ≤ alpha → 0 ≤ Cnorm →
      0 < se → 0 ≤ sf → 0 ≤ nu → 0 ≤ fsup → 0 ≤ upper →
      ∀ (U : SpatialCoordinates d → ℝ) (cq : ℝ),
      IsHolderOn alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + r • x) - cq) →
      cAlphaNorm alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + r • x) - cq) ≤
        Cnorm * r ^ ((2 - (d : ℝ)) / 2) * se ^ (-(1 : ℝ) / 2) * Real.sqrt nu +
          Cnorm * r ^ (2 : ℝ) * se⁻¹ * fsup →
      ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
          ‖u.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
        (a : PositiveCoefficient (centeredCube z r hr)),
        I.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 ≤ upper * sf →
      ∀ (datum : weakSobolevGraph (centeredCube z r hr)) (B : SpatialCoordinates d → ℝ),
        ContinuousOn B (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
        ((datum.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube z r hr : Set (SpatialCoordinates d))] B) →
        EqOn B U (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) →
        dirichletResponse (killedResponseSpace hP) a datum ≤
          (2 * (Ce * upper) * ((Real.sqrt d) ^ (alpha - beta) * Cnorm) ^ 2) * (sf / se) *
            (nu + se⁻¹ * r ^ ((d : ℝ) + 2) * fsup ^ 2) := by
  obtain ⟨Ce, hCe, hResponse⟩ := goodext_dirichlet_response_bound d hd I X Sob beta hbeta
  refine ⟨Ce, hCe, ?_⟩
  intro z r hr hr1 alpha Cnorm se sf nu fsup upper hba hCnorm hse hsf hnu hf hupper
    U cq hHolder hNorm hP a hLam datum B hBc hBr hBt
  let amp := Cnorm * r ^ ((2 - (d : ℝ)) / 2) * se ^ (-(1 : ℝ) / 2) * Real.sqrt nu +
    Cnorm * r ^ (2 : ℝ) * se⁻¹ * fsup
  have hamp : 0 ≤ amp := by
    dsimp only [amp]
    positivity
  obtain ⟨hTraceHolder, hTrace⟩ := scaled_boundary_holderSeminorm_le_normalized_norm
    z r hr alpha beta cq amp hba (by linarith only [hbeta.1]) hamp U hHolder hNorm
  let trace := r ^ beta * holderSeminorm beta (frontier (Metric.ball z (r / 2))) U
  let C := (Real.sqrt d) ^ (alpha - beta) * Cnorm
  have hTraceBound : trace ≤ C * r ^ ((2 - (d : ℝ)) / 2) * se ^ (-(1 : ℝ) / 2) *
      Real.sqrt nu + C * r ^ (2 : ℝ) * se⁻¹ * fsup := by
    exact hTrace.trans_eq (by dsimp only [amp, C]; ring)
  have hEnergy := hResponse z r hr hr1 hP a U (upper * sf) hLam hTraceHolder datum B hBc hBr hBt
  apply trace_energy_le_reference_ratio d trace C (Ce * upper) r se sf nu fsup
    (dirichletResponse (killedResponseSpace hP) a datum)
  · exact mul_nonneg (Real.rpow_nonneg hr.le _) (holderSeminorm_nonneg _ _ _)
  · exact mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) hCnorm
  · exact mul_nonneg hCe.le hupper
  · exact hr
  · exact hse
  · exact hsf
  · exact hnu
  · exact hf
  · exact hTraceBound
  · exact hEnergy.trans_eq (by change Ce * (upper * sf) * r ^ ((d : ℝ) - 2) * trace ^ 2 = _; ring)
end Paper
