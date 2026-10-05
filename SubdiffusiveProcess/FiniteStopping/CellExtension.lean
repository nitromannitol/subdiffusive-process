module

public import SubdiffusiveProcess.FiniteStopping.CellRegularity

@[expose] public section

/-! The extension estimate (clause (iii) of `SubdiffusiveProcess.Paper.lem_finite_good_cell`) as a predicate of a cell,
next to `Reg` (clause (ii)); it is not asserted to hold. -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.FiniteStopping

variable {d : ℕ}

/-- The extension estimate of `lem_finite_good_cell` (clause (iii), infrared field `H`) for the cell of side
`3^{-k}` centred at `z` at cutoff `N`: for every `C^β` trace `G` on `∂Q`, the Dirichlet response of the
actual cutoff coefficient is at most `Aext r^{d-2} s ‖G‖²_{C^β/ℝ}`, where `s` is the reference scalar
`(κ_{N-k}/κ_N) e^{H(z)+Σ_{j<k} ω_{-j}(z)}`. -/
def Ext
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (beta Aext : ℝ)
    (N k : ℕ) (z : SpatialCoordinates d) (omega : BilateralField d) : Prop :=
  let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
  let hr : 0 < r := by positivity
  let Q : Opens (SpatialCoordinates d) := centeredCube z r hr
  let closedQ : Set (SpatialCoordinates d) := closedCube z r hr
  let T : SpatialCoordinates d → SpatialCoordinates d := fun x => z + r • x
  let kappa : ℕ → ℝ := fun J =>
    Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
      SubdiffusiveProcess.CoarseGrainingVocab.ahom model J
  let s : ℝ := (kappa (N - k) / kappa N) *
    Real.exp ((H omega) z + ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z)
  let aQ : PositiveCoefficient Q := cutoffPositiveCoefficient model H omega N z hr
  ∀ hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
      ‖(u : SobolevData Q).1‖ ≤ K * ‖@subspaceGradient d Q (killedSobolevGraph Q) u‖,
    ∀ (b : weakSobolevGraph Q) (G : SpatialCoordinates d → ℝ),
      ContinuousOn G closedQ → @IsHolderOn d beta (frontier (Q : Set (SpatialCoordinates d))) G →
      ((fun x => (b : SobolevData Q).1 x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] G) →
      ∀ c : ℝ,
      @dirichletResponse d Q (@killedResponseSpace d Q hP) aQ b ≤
        Aext * r ^ ((d : ℝ) - 2) * s *
          (@cAlphaNorm d beta
            (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))
            (fun x => G (T x) - c)) ^ (2 : ℕ)

end SubdiffusiveProcess.FiniteStopping
