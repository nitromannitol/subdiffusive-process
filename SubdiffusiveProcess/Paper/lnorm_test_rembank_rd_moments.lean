module

public import SubdiffusiveProcess.Main.CutoffCoefficient
public import Homogenization.Sobolev.H1.BasicLemmas
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.EllipticRegularity.CubeDilation
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Tactic
public import Mathlib
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.EllipticRegularity.Bridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ScalarFieldPackaging
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerReduction
public import SubdiffusiveProcess.Probability.ConditionalPullback
public import SubdiffusiveProcess.Sobolev.AffineData
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.ResponseMoments.Interfaces
public import SubdiffusiveProcess.Lnorm.BoundaryResponseFamily
public import SubdiffusiveProcess.Lnorm.LayerRegroup
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.rem_bank

@[expose] public section

/-! This module establishes lnorm_test_rembank_rd_moments for the cutoff-response compactness construction;
it does not identify subsequential limits or assert local-normalization convergence. -/

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Metric
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SubdiffusiveProcess.Paper

section


/-- lnorm test rembank rd moments for the cutoff-response compactness construction. -/
theorem lnorm_test_rembank_rd_moments
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (W : SmallPerturbationInput d) (Sf : SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d ⟨by omega⟩) :
    ∃ (q : ℝ) (delta0 : ℝ), 2 < q ∧ 0 < delta0 ∧
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
    ∀ (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
      (phi : SpatialCoordinates d → ℝ) (_hphi : ContDiff ℝ ∞ phi)
      (b : weakSobolevGraph (centeredCube z r hr))
      (_hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi),
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (_Rm : in_responses d M) (Sreg : in_6_16 d M) (_It : in_iteration d M Jc Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ))
      (_hH : InfraredCharacterization M H),
      M.delta ≤ min 1 delta0 →
      let Pm : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
      let a : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr) :=
        fun N omega => cutoffPositiveCoefficient M H omega N z hr
      let RD : ℕ → BilateralField d → ℝ :=
        fun N omega => dirichletResponse (killedResponseSpace hP) (a N omega) b
      ∃ Cmom : ℝ, 0 ≤ Cmom ∧
        ∀ N, MemLp (RD N) (ENNReal.ofReal 6) Pm ∧ MemLp (RD N) (ENNReal.ofReal q) Pm ∧
          eLpNorm (RD N) (ENNReal.ofReal 6) Pm ≤ ENNReal.ofReal Cmom ∧
          eLpNorm (RD N) (ENNReal.ofReal q) Pm ≤ ENNReal.ofReal Cmom := by
  have ht0 : (d : ℝ) - 1 < (d : ℝ) - 1 / 2 := by linarith only [hd]
  have ht1 : (d : ℝ) - 1 / 2 < (d : ℝ) := by linarith only [hd, ht0]
  obtain ⟨aexpOf, qOf, ordersOf, thresholdOf, _, _, haexppos, haexpeq, hmain⟩ :=
    rem_bank d hd Jc Pc Xc W Sf D ((d : ℝ) - 1 / 2) ht0 ht1
  obtain ⟨hpq, hdeltapos, h3p, hqmem, h12p, h4q, hall⟩ := hmain 2 (by norm_num)
  refine ⟨qOf 2 d ((d:ℝ) - 1/2), thresholdOf d ((d:ℝ)-1/2) (ordersOf 2 d ((d:ℝ)-1/2)),
    by linarith only [hd, ht0, ht1, haexppos, haexpeq, hpq, hdeltapos], hdeltapos, ?_⟩
  intro z r hr hrle hP phi hphi b hb M Rm Sreg It H hH hdelta Pm a RD
  obtain ⟨hdir, -, -⟩ := hall M Rm Sreg It H hH hdelta
  obtain ⟨KD, KK, B, hB0, -, hmemLp, hnormsum⟩ :=
    hdir z r hr hrle hP phi hphi b hb (0 : SpatialCoordinates d → ℝ) contDiff_const
      HasCompactSupport.zero (by simp only [tsupport_zero, empty_subset]) (domainConstantL2 (Ω := centeredCube z r hr) 0)
      (domainConstantL2_coeFn 0)
  have h6 : (3 : ℝ) * 2 = 6 := by norm_num
  rw [h6] at hnormsum hmemLp
  refine ⟨B, hB0, fun N => ⟨(hmemLp N).2.2.1, (hmemLp N).2.2.2.2.1,
    SubdiffusiveProcess.Lnorm.ennreal_le_of_add_six (hnormsum N)⟩⟩

end

end SubdiffusiveProcess.Paper
