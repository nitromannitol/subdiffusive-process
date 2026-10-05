module

public import SubdiffusiveProcess.Paper.density_finite_source_response
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology ContDiff BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper
/-- Pass the actual finite harmonic-energy bound to its subsequential limit.
The original weak datum need not itself have a continuous representative:
the continuous harmonic minimizer supplies the same exact boundary response. -/
theorem density_source_energy_limit
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
        (a : ℕ → PositiveCoefficient (centeredCube z r hr)),
        (∀ᶠ n in atTop, I.Lam z r hr (a n) z r ((beta - 1 / 2) / 4) 2 ≤ upper * sf) →
      ∀ (datum : weakSobolevGraph (centeredCube z r hr)) (VN : ℕ → SpatialCoordinates d → ℝ),
        (∀ n, ContinuousOn (VN n) (closure (centeredCube z r hr : Set (SpatialCoordinates d)))) →
        (∀ n, ((dirichletMinimizer (killedResponseSpace hP) (a n) datum).val.1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] VN n) →
        (∀ n, EqOn (VN n) U (frontier (centeredCube z r hr : Set (SpatialCoordinates d)))) →
      ∀ cost : ℝ, Tendsto (fun n => dirichletResponse (killedResponseSpace hP) (a n) datum)
        atTop (𝓝 cost) →
        cost ≤
          (2 * (Ce * upper) * ((Real.sqrt d) ^ (alpha - beta) * Cnorm) ^ 2) * (sf / se) *
            (nu + se⁻¹ * r ^ ((d : ℝ) + 2) * fsup ^ 2) := by
  obtain ⟨Ce, hCe, hResponse⟩ := density_finite_source_response d hd I X Sob beta hbeta
  refine ⟨Ce, hCe, ?_⟩
  intro z r hr hr1 alpha Cnorm se sf nu fsup upper hba hCnorm hse hsf hnu hf hupper
    U cq hHolder hNorm hP a hLam datum VN hVc hVr hVt cost hcost
  apply le_of_tendsto hcost
  filter_upwards [hLam] with n hn
  have hBound := hResponse z r hr hr1 alpha Cnorm se sf nu fsup upper hba hCnorm hse
    hsf hnu hf hupper U cq hHolder hNorm hP (a n) hn
    (dirichletMinimizer (killedResponseSpace hP) (a n) datum) (VN n) (hVc n) (hVr n) (hVt n)
  have hsame := dirichletResponse_eq_of_sub_mem (killedResponseSpace hP) (a n)
    (dirichletMinimizer (killedResponseSpace hP) (a n) datum) datum
    (dirichletMinimizer_mem_affine (killedResponseSpace hP) (a n) datum)
  rw [hsame] at hBound
  exact hBound
end SubdiffusiveProcess.Paper
