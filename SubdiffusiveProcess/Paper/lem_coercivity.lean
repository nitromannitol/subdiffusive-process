import SubdiffusiveProcess.Main.OriginalGridResponseConvolution
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.CubeNegativeL2Norm
import SubdiffusiveProcess.Main.HalfFractionalOrder
import SubdiffusiveProcess.Sobolev.BoundaryEnergy
import SubdiffusiveProcess.Sobolev.FoldDiscounts
import SubdiffusiveProcess.Sobolev.LoadApproximation
import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Sobolev.AffineResponses
import SubdiffusiveProcess.Probability.GMCFieldLaws
import SubdiffusiveProcess.CoarseGrainingVocab.Core
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
import SubdiffusiveProcess.Frozen.Section6.Defs.GoodEvent
import SubdiffusiveProcess.Frozen.Section6.Defs.HolderRegularityConclusions
import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.lane4_besov_h34_coercivity
import SubdiffusiveProcess.Paper.lane4_coercivity_dilation
import SubdiffusiveProcess.Paper.lane4_lambda_inv_moments

import SubdiffusiveProcess.Analysis.MeasurableMajorant
import SubdiffusiveProcess.Analysis.CutoffInverseEnvelope
import SubdiffusiveProcess.Paper.lem_extension_cell_moment
import SubdiffusiveProcess.Paper.lane4_lambda_inv_cell_moment

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Actual chart measurability before any disorder reduction or moment order. -/
theorem aux_lem_coercivity_lambda_inv_aesm {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    AEStronglyMeasurable (fun om : BilateralField d =>
      (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹)
      (chaosSampleLaw M).toMeasure := by
  let Y : ℕ → BilateralField d → ℝ := fun n om =>
    Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
      (Homogenization.originCube d 0) (-(n : ℤ))
      (E.chart z r hr (cutoffPositiveCoefficient M H om N z hr) z r)
  have hY : ∀ n, AEStronglyMeasurable (Y n) (chaosSampleLaw M).toMeasure := by
    intro n
    simpa only [Y, Homogenization.originCube, zero_sub] using
      aux_lem_extension_cell_moment_aesm_maxS_chart hd E M H hH N z r hr z r hr
        Set.Subset.rfl n
  have hsum : ∀ om, Summable (fun n : ℕ =>
      Homogenization.Book.Ch02.geometricWeight s 1 n * Real.rpow (Y n om) (1 / 2)) := by
    intro om
    exact (aux_lane4_lambda_inv_moments_lam_inv_eq E z r hr
      (cutoffPositiveCoefficient M H om N z hr) s hs0 hs1).choose_spec.2.1
  have hmeas := aux_lane4_lambda_inv_moments_Ssum_meas
    (chaosSampleLaw M).toMeasure s Y hY hsum
  have heq : (fun om : BilateralField d =>
      (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹) =
      fun om => (∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s 1 n *
        Real.rpow (Y n om) (1 / 2)) ^ 2 := by
    funext om
    obtain ⟨Ssum, _, _, hseq, heq⟩ := aux_lane4_lambda_inv_moments_lam_inv_eq E z r hr
      (cutoffPositiveCoefficient M H om N z hr) s hs0 hs1
    rw [heq, hseq]
  rw [heq]
  exact (continuous_pow 2).comp_aestronglyMeasurable hmeas

/-- A compact reciprocal-coefficient envelope bounds the actual inverse lambda
at every sample, including the exceptional set of its measurable version. -/
theorem aux_lem_coercivity_lambda_inv_le_envelope {d : ℕ} (hd : 2 ≤ d)
    (E : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) (om : BilateralField d) :
    (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹ ≤
      SubdiffusiveProcess.Analysis.compactCutoffInverseEnvelope M H N (closedCube z r hr) om := by
  haveI : NeZero d := ⟨by omega⟩
  let X := SubdiffusiveProcess.Analysis.compactCutoffInverseEnvelope M H N (closedCube z r hr) om
  have hX : 0 ≤ X := (SubdiffusiveProcess.Analysis.compactCutoffInverseEnvelope_pos M H N _ om).le
  let Y : ℕ → ℝ := fun n =>
    Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
      (Homogenization.originCube d 0) (-(n : ℤ))
      (E.chart z r hr (cutoffPositiveCoefficient M H om N z hr) z r)
  have hYn : ∀ n, 0 ≤ Y n := fun n => aux_lane4_lambda_inv_moments_Y_nonneg _ _
  have hYX : ∀ n, Y n ≤ X := by
    intro n
    have hk : -(n : ℤ) ≤ (Homogenization.originCube d 0).scale := by
      change -(n : ℤ) ≤ 0
      omega
    apply Homogenization.Book.Ch02.finsetSupReal_le _
      (Homogenization.descendantsAtScale_nonempty (Homogenization.originCube d 0) hk)
    intro Q hQ
    have hsub : Homogenization.openCubeSet Q ⊆
        Homogenization.openCubeSet (Homogenization.originCube d 0) := by
      rw [Homogenization.descendantsAtScale_eq_descendantsAtDepth _ hk] at hQ
      exact Homogenization.openCubeSet_subset_of_mem_descendantsAtDepth hQ
    apply aux_lane4_lambda_inv_cell_moment_cell_le_of_inv_le E M H om N z r hr Q hsub X hX
    intro x hx
    exact SubdiffusiveProcess.Analysis.cutoffCoefficient_inv_le_compactEnvelope M H N _ om _
      (centeredCube_subset_closedCube z hr
        (aux_lem_extension_cell_moment_affine_mem z r hr (hsub hx)))
  obtain ⟨Ssum, hSnonneg, hsummable, hseq, hlam⟩ :=
    aux_lane4_lambda_inv_moments_lam_inv_eq E z r hr
      (cutoffPositiveCoefficient M H om N z hr) s hs0 hs1
  obtain ⟨hwsum, hwsummable, hwnn⟩ := aux_lane4_lambda_inv_moments_weight_sum s hs0
  have hSbound : Ssum ≤ Real.sqrt X := by
    rw [hseq]
    calc
      (∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s 1 n *
          Real.rpow (Y n) (1 / 2)) ≤
          ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s 1 n * Real.sqrt X := by
        apply Summable.tsum_le_tsum _ hsummable (hwsummable.mul_right _)
        intro n
        apply mul_le_mul_of_nonneg_left _ (hwnn n)
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow (hYn n) (hYX n) (by norm_num)
      _ = (∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s 1 n) * Real.sqrt X :=
        tsum_mul_right
      _ = Real.sqrt X := by rw [hwsum, one_mul]
  rw [hlam]
  exact (pow_le_pow_left₀ hSnonneg hSbound 2).trans_eq (Real.sq_sqrt hX)

/-- Source `mfd:lem-coercivity`, live paper lines 8574–8585. The same measurable
constant is chosen before p and dominates both actual pointwise coercivity
inequalities. The original inverse-lambda constant is replaced only on a
measurable null set, with a literal compact reciprocal-coefficient envelope;
all moments are unchanged. No hypothesis or disorder restriction is added. -/
theorem lem_coercivity :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_S : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd),
  ∃ delta0 : ℝ → ℝ, (∀ p : ℝ, 1 ≤ p → 0 < delta0 p) ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∃ K : ℕ → BilateralField d → ℝ,
        (∀ N : ℕ, Measurable (K N)) ∧
        (∀ (N : ℕ) (om : BilateralField d),
          (∀ v : killedSobolevGraph (centeredCube z r hr),
            cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
                (fun _ : Fin 1 => (v : SobolevData (centeredCube z r hr)).1) < ⊤ ∧
            cubeFractionalSqNorm hd z r hr threeQuarterOrder
                (v : SobolevData (centeredCube z r hr)).1 ≤
              K N om * sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
                (v : SobolevData (centeredCube z r hr))
                (v : SobolevData (centeredCube z r hr))) ∧
          (∀ v : meanZeroSobolevGraph (centeredCube z r hr),
            cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
                (fun _ : Fin 1 => (v : SobolevData (centeredCube z r hr)).1) < ⊤ ∧
            cubeFractionalSqNorm hd z r hr threeQuarterOrder
                (v : SobolevData (centeredCube z r hr)).1 ≤
              K N om * sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
                (v : SobolevData (centeredCube z r hr))
                (v : SobolevData (centeredCube z r hr)))) ∧
        (∀ p : ℝ, 1 ≤ p → M.delta ≤ delta0 p →
          ∃ Cbound : ℝ,
            (∀ N, MemLp (K N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
            (∀ N, eLpNorm (K N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
              ENNReal.ofReal Cbound)) := by
  intro d hd _ _ E P S
  have hs : (1 / 8 : ℝ) ∈ Set.Ioo (0 : ℝ) (1 / 4) := by
    constructor <;> norm_num
  obtain ⟨delta0, hdelta0, hmoment⟩ :=
    lane4_lambda_inv_moments d hd E (1 / 8 : ℝ) hs
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm H hH z r hr hrle
  obtain ⟨C, hC, hunit⟩ :=
    lane4_besov_h34_coercivity d hd E P S (1 / 8 : ℝ) hs
  have horigin :
      ∀ (hr : (0 : ℝ) < 1)
        (a : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 hr)),
        (∀ v : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 hr),
          cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 hr threeQuarterOrder
              (v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 hr)).1 ≤
            C * (E.lam (0 : SpatialCoordinates d) 1 hr a
              (0 : SpatialCoordinates d) 1 (1 / 8 : ℝ) 1)⁻¹ *
              sobolevCoefficientForm a
                (v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 hr))
                (v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 hr))) ∧
        (∀ v : meanZeroSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 hr),
          cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 hr threeQuarterOrder
              (v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 hr)).1 ≤
            C * (E.lam (0 : SpatialCoordinates d) 1 hr a
              (0 : SpatialCoordinates d) 1 (1 / 8 : ℝ) 1)⁻¹ *
              sobolevCoefficientForm a
                (v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 hr))
                (v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 hr))) := by
    intro h1 a
    constructor
    · intro v
      exact (hunit (0 : SpatialCoordinates d) h1 a).1 v |>.2
    · intro v
      exact (hunit (0 : SpatialCoordinates d) h1 a).2 v |>.2
  obtain ⟨C', hC', hcoercive⟩ :=
    lane4_coercivity_dilation d hd E (1 / 8 : ℝ) hs C hC horigin z r hr hrle
  let Kraw : ℕ → BilateralField d → ℝ := fun N om =>
    C' * (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr)
      z r (1 / 8 : ℝ) 1)⁻¹
  have hrawmeas : ∀ N, AEStronglyMeasurable (Kraw N) (chaosSampleLaw M).toMeasure := by
    intro N
    exact (aux_lem_coercivity_lambda_inv_aesm hd E M H hH.1 N z r hr
      (1 / 8 : ℝ) hs.1 (by norm_num)).const_mul C'
  have hrawle : ∀ N om, Kraw N om ≤
      C' * SubdiffusiveProcess.Analysis.compactCutoffInverseEnvelope M H N (closedCube z r hr) om := by
    intro N om
    exact mul_le_mul_of_nonneg_left
      (aux_lem_coercivity_lambda_inv_le_envelope hd E M H N z r hr
        (1 / 8 : ℝ) hs.1 (by norm_num) om) hC'.le
  have hexists : ∀ N, ∃ k : BilateralField d → ℝ, Measurable k ∧
      (∀ om, Kraw N om ≤ k om) ∧ Kraw N =ᵐ[(chaosSampleLaw M).toMeasure] k := by
    intro N
    exact SubdiffusiveProcess.Analysis.exists_measurable_majorant_ae_eq (chaosSampleLaw M).toMeasure
      (Kraw N) (fun om => C' *
        SubdiffusiveProcess.Analysis.compactCutoffInverseEnvelope M H N (closedCube z r hr) om)
      (hrawmeas N).aemeasurable
      (measurable_const.mul
        (SubdiffusiveProcess.Analysis.measurable_compactCutoffInverseEnvelope M H hH.1 N _))
      (hrawle N)
  choose K hKmeas hKle hKae using hexists
  refine ⟨K, hKmeas, ?_, ?_⟩
  · intro N om
    constructor
    · intro v
      have hu : (v : SobolevData (centeredCube z r hr)) ∈
          weakSobolevGraph (centeredCube z r hr) :=
        killedSobolevGraph_le_weakSobolevGraph v.property
      let u : weakSobolevGraph (centeredCube z r hr) :=
        ⟨(v : SobolevData (centeredCube z r hr)), hu⟩
      have hfinite := S.h1_fractional_finite z r hr u
      refine ⟨?_, ?_⟩
      · simpa [u] using hfinite
      · have hbase := (hcoercive (cutoffPositiveCoefficient M H om N z hr)).1 v
        change cubeFractionalSqNorm hd z r hr threeQuarterOrder
          (v : SobolevData (centeredCube z r hr)).1 ≤
            Kraw N om * sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
              (v : SobolevData (centeredCube z r hr))
              (v : SobolevData (centeredCube z r hr)) at hbase
        exact hbase.trans (mul_le_mul_of_nonneg_right (hKle N om)
          (sobolevCoefficientForm_nonneg _ _))
    · intro v
      have hu : (v : SobolevData (centeredCube z r hr)) ∈
          weakSobolevGraph (centeredCube z r hr) :=
        (inf_le_left : meanZeroSobolevGraph (centeredCube z r hr) ≤
          weakSobolevGraph (centeredCube z r hr)) v.property
      let u : weakSobolevGraph (centeredCube z r hr) :=
        ⟨(v : SobolevData (centeredCube z r hr)), hu⟩
      have hfinite := S.h1_fractional_finite z r hr u
      refine ⟨?_, ?_⟩
      · simpa [u] using hfinite
      · have hbase := (hcoercive (cutoffPositiveCoefficient M H om N z hr)).2 v
        change cubeFractionalSqNorm hd z r hr threeQuarterOrder
          (v : SobolevData (centeredCube z r hr)).1 ≤
            Kraw N om * sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
              (v : SobolevData (centeredCube z r hr))
              (v : SobolevData (centeredCube z r hr)) at hbase
        exact hbase.trans (mul_le_mul_of_nonneg_right (hKle N om)
          (sobolevCoefficientForm_nonneg _ _))
  · intro p hp hδ
    obtain ⟨Cbound, hmem, hbound⟩ :=
      hmoment M Rm H hH z r hr hrle p hp hδ
    refine ⟨C' * Cbound, ?_, ?_⟩
    · intro N
      exact MemLp.ae_eq (hKae N) ((hmem N).const_mul C')
    · intro N
      rw [← eLpNorm_congr_ae (hKae N)]
      calc
        eLpNorm (Kraw N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
            ‖C'‖ₑ *
              eLpNorm
                (fun om : BilateralField d =>
                  (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr)
                    z r (1 / 8 : ℝ) 1)⁻¹)
                (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure := by
          simpa [Kraw, Pi.smul_apply, smul_eq_mul] using
            (eLpNorm_const_smul_le
              (c := C')
              (f := fun om : BilateralField d =>
                (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr)
                  z r (1 / 8 : ℝ) 1)⁻¹)
              (p := ENNReal.ofReal p)
              (μ := (chaosSampleLaw M).toMeasure))
        _ ≤ ‖C'‖ₑ * ENNReal.ofReal Cbound := by
          gcongr
          exact hbound N
        _ = ENNReal.ofReal (C' * Cbound) := by
          rw [Real.enorm_eq_ofReal hC'.le, ENNReal.ofReal_mul hC'.le]


/-- Exact original-header compatibility for existing coercivity consumers. -/
theorem aux_lem_coercivity_compat :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_S : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd),
  ∃ delta0 : ℝ → ℝ, (∀ p : ℝ, 1 ≤ p → 0 < delta0 p) ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∃ K : ℕ → BilateralField d → ℝ,
        (∀ (N : ℕ) (om : BilateralField d),
          (∀ v : killedSobolevGraph (centeredCube z r hr),
            cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
                (fun _ : Fin 1 => (v : SobolevData (centeredCube z r hr)).1) < ⊤ ∧
            cubeFractionalSqNorm hd z r hr threeQuarterOrder
                (v : SobolevData (centeredCube z r hr)).1 ≤
              K N om * sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
                (v : SobolevData (centeredCube z r hr))
                (v : SobolevData (centeredCube z r hr))) ∧
          (∀ v : meanZeroSobolevGraph (centeredCube z r hr),
            cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
                (fun _ : Fin 1 => (v : SobolevData (centeredCube z r hr)).1) < ⊤ ∧
            cubeFractionalSqNorm hd z r hr threeQuarterOrder
                (v : SobolevData (centeredCube z r hr)).1 ≤
              K N om * sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
                (v : SobolevData (centeredCube z r hr))
                (v : SobolevData (centeredCube z r hr)))) ∧
        (∀ p : ℝ, 1 ≤ p → M.delta ≤ delta0 p →
          ∃ Cbound : ℝ,
            (∀ N, MemLp (K N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
            (∀ N, eLpNorm (K N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
              ENNReal.ofReal Cbound)) := by
  intro d hd _ _ E P S
  obtain ⟨delta0, hdelta0, hall⟩ := lem_coercivity d hd E P S
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm H hH z r hr hrle
  obtain ⟨K, _, hcoer, hmom⟩ := hall M Rm H hH z r hr hrle
  exact ⟨K, hcoer, hmom⟩

end Paper
