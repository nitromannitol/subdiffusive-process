module

public import SubdiffusiveProcess.Paper.aux_test_prop16_rd_band
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import Homogenization.Sobolev.H1.BasicLemmas
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Lane4.CubeDilation
public import SubdiffusiveProcess.Lane4.Inputs
public import SubdiffusiveProcess.Lane2.BoundaryResponse
public import SubdiffusiveProcess.Lane2.ExternalInputs
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import Mathlib.Analysis.Seminorm
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Tactic
public import Mathlib
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.Lane4.Bridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ScalarFieldPackaging
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerReduction
public import SubdiffusiveProcess.Probability.ConditionalPullback
public import SubdiffusiveProcess.Sobolev.AffineData
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Lane3.Interfaces
public import SubdiffusiveProcess.Lnorm.BoundaryMomentAlgebra
public import SubdiffusiveProcess.Lnorm.BoundaryResponseFamily
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.prop_16
public import SubdiffusiveProcess.Paper.rem_bank

@[expose] public section

/-! This module establishes lnorm_test_prop16_rd_band for the cutoff-response compactness construction;
it does not identify subsequential limits or assert local-normalization convergence. -/

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Metric
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Paper

section


/-- lnorm test prop16 rd band for the cutoff-response compactness construction. -/
theorem lnorm_test_prop16_rd_band
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (W : SmallPerturbationInput d) (Sf : SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d ⟨by omega⟩) :
    ∃ (delta0 : ℝ), 0 < delta0 ∧
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
    ∀ (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
      (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ ∞ phi)
      (hnonconst : ∃ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∃ y ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), phi x ≠ phi y)
      (b : weakSobolevGraph (centeredCube z r hr))
      (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi),
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ))
      (hH : InfraredCharacterization M H),
      M.delta ≤ min 1 delta0 →
      let Pm : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
      let a : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr) :=
        fun N omega => cutoffPositiveCoefficient M H omega N z hr
      let RD : ℕ → BilateralField d → ℝ :=
        fun N omega => dirichletResponse (killedResponseSpace hP) (a N omega) b
      ∃ Cband : ℝ, 0 < Cband ∧
        ∀ (h N : ℕ),
          eLpNorm (fun omega => RD N omega -
              (Pm[RD N | bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) omega)
            (ENNReal.ofReal 2) Pm ≤
          ENNReal.ofReal (Cband * M.delta * (3 : ℝ) ^ (-(SubdiffusiveProcess.Lnorm.prop16_aD d) * (h : ℝ))) := by
  exact aux_test_prop16_rd_band d hd Jc Pc Xc W Sf D 2 le_rfl

end

end Paper
