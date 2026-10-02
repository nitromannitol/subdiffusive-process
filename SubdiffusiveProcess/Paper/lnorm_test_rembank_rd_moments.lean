import SubdiffusiveProcess.Main.CutoffCoefficient
import Homogenization.Sobolev.H1.BasicLemmas
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Lane4.CubeDilation
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Lane2.ExternalInputs
import SubdiffusiveProcess.Sobolev.DirichletResponse
import Mathlib.Analysis.Seminorm
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Tactic
import Mathlib
import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
import SubdiffusiveProcess.Sobolev.DomainPoincare
import SubdiffusiveProcess.Lane4.Bridge
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ScalarFieldPackaging
import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerReduction
import SubdiffusiveProcess.Probability.ConditionalPullback
import SubdiffusiveProcess.Sobolev.AffineData
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Lane3.Interfaces
import SubdiffusiveProcess.Lnorm.BoundaryResponseFamily
import SubdiffusiveProcess.Lnorm.LayerRegroup
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Paper.rem_bank

/-! This module establishes lnorm_test_rembank_rd_moments for the cutoff-response compactness construction;
it does not identify subsequential limits or assert local-normalization convergence. -/

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Metric
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Paper

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
      (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ ∞ phi)
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
  intro z r hr hrle hP phi hphi b hb M Rm Sreg It H hH hdelta
  intro Pm a RD
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

end Paper
