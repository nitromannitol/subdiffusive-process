module

public import SubdiffusiveProcess.Paper.in_joint_extracted_candidates
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators Topology

namespace Paper
noncomputable section


/-- The volume-normalized affine Dirichlet response of the cutoff coefficient (cutoff `N`) on the
observation cell of level `k`, exactly as it enters the `hAE`/`hAF` limits of `prop_conc`. -/
def aux_prop_conc_setup_resp {d : ℕ} (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (zcell : SpatialCoordinates d) (k : ℕ)
    (hPk : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
        (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _)),
      ‖(u : SobolevData
          (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))).1‖ ≤
        K * ‖subspaceGradient
          (killedSobolevGraph
            (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))) u‖)
    (N : ℕ) (om : BilateralField d) (pvec : Fin d → ℝ) : ℝ :=
  affineDirichletResponse
      (centeredCube_isBounded zcell
        (Real.rpow_pos_of_pos zero_lt_three _))
      hPk
      (Lane4.cutoffPositiveCoefficient model H om N zcell
        (Real.rpow_pos_of_pos zero_lt_three _)) pvec /
    (volume
      (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ)))
        (Real.rpow_pos_of_pos zero_lt_three _) : Set (SpatialCoordinates d))).toReal

/-- The standing data of `prop_conc` (single observation level `k`, one cell `cellIdx`, one padded cell
`paddedIdx`) once `C0` is fixed: exactly its binders `hJoint`, `hm hmM hM`, `horder`, `hcell`, `hpaddedIdx`,
`hsymAE`, `hsymAF`, `hAE`, `hAF` (nothing added, nothing removed). -/
def prop_conc_setup (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace
      (centeredCube (z i) (r i) (hr i)))
    (GN : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (C0 m M : ℝ) (zcell : SpatialCoordinates d) (k : ℕ)
    (cellIdx paddedIdx : ℕ)
    (hPk : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
        (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _)),
      ‖(u : SobolevData
          (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))).1‖ ≤
        K * ‖subspaceGradient
          (killedSobolevGraph
            (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))) u‖)
    (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ) : Prop :=
  in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF ∧
  (C0⁻¹ ≤ m ∧ m ≤ M ∧ M ≤ C0) ∧
  (∀ᵐ omega ∂P, ∀ i,
    limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
      ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
        u ∈ limitFormDomain (GE i omega) →
          m * (limitFormEnergy (GE i omega) u).toReal ≤
              (limitFormEnergy (GF i omega) u).toReal ∧
            (limitFormEnergy (GF i omega) u).toReal ≤
              M * (limitFormEnergy (GE i omega) u).toReal) ∧
  (z cellIdx = zcell ∧ r cellIdx = (3 : ℝ) ^ (-(k : ℝ))) ∧
  (z paddedIdx = zcell ∧ r paddedIdx = 3 * ((3 : ℝ) ^ (-(k : ℝ)))) ∧
  (∀ omega, (AE omega).transpose = AE omega) ∧
  (∀ omega, (AF omega).transpose = AF omega) ∧
  (∀ᵐ omega ∂P, ∀ pvec : Fin d → ℝ,
    Tendsto (fun j : ℕ => aux_prop_conc_setup_resp model H zcell k hPk (NE j) (field omega) pvec)
      atTop (𝓝 (pvec ⬝ᵥ (AE omega).mulVec pvec))) ∧
  (∀ᵐ omega ∂P, ∀ pvec : Fin d → ℝ,
    Tendsto (fun j : ℕ => aux_prop_conc_setup_resp model H zcell k hPk (NF j) (field omega) pvec)
      atTop (𝓝 (pvec ⬝ᵥ (AF omega).mulVec pvec)))

end
end Paper
