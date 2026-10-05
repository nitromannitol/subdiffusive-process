module

public import SubdiffusiveProcess.Paper.lem_as_coarse_scalar_cell_bridge
public import SubdiffusiveProcess.Paper.lem_as_coarse_first_clause_assembly

@[expose] public section

open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open Homogenization.Book.Ch02

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Pointwise scalar extremes bounds supply exactly the late-cell bounds of the
first-clause assembly, at every cutoff beyond its selected starting index. -/
theorem lem_as_coarse_scalar_consumer {d : ℕ}
    (hd : 2 ≤ d) (Jc : in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (mlow mhigh : ℕ → BilateralField d → ℝ)
    (hext : ∀ N : ℕ, 0 < mlow N om ∧
      ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
        mlow N om ≤ cutoffCoefficient M H om N x ∧
          cutoffCoefficient M H om N x ≤ mhigh N om)
    (m N0 : ℕ) :
    (∀ N, 0 ≤ mhigh N om + (mlow N om)⁻¹) ∧
      (∀ N, N0 ≤ N → ∀ n : ℕ, N < n + m →
        ∀ R ∈ aux_lem_as_coarse_ms_desc d n,
          coarseBMatrixNorm R
              (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) z r) ≤
              mhigh N om + (mlow N om)⁻¹ ∧
            coarseSigmaStarInvMatrixNorm R
              (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) z r) ≤
              mhigh N om + (mlow N om)⁻¹) := by
  obtain ⟨hS, hcell⟩ :=
    lem_as_coarse_scalar_cell_bridge hd Jc M H om z r hr mlow mhigh hext
  refine ⟨hS, ?_⟩
  intro N _ n _ R hR
  exact hcell N n R hR

end SubdiffusiveProcess.Paper
