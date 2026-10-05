module

public import SubdiffusiveProcess.EllipticRegularity.Bridge
public import SubdiffusiveProcess.EllipticRegularity.ProbeAssembly
public import SubdiffusiveProcess.EllipticRegularity.FoldedProbe
public import SubdiffusiveProcess.Sobolev.FoldDiscounts
public import SubdiffusiveProcess.CoarseGrainingVocab.Core
public import SubdiffusiveProcess.CoarseGrainingVocab.HomogenizationErrorDefault
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6AnnularCarrier
public import SubdiffusiveProcess.Paper.cor_fold
public import SubdiffusiveProcess.Paper.folded_probe_discounted_le
public import SubdiffusiveProcess.Paper.lem_repair_err_fold_carrier_bridge

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

attribute [local instance] Classical.propDecidable



theorem lem_repair_err_fold_paper_comparison :
  ∀ (d : ℕ) (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)],
  ∀ (s : ℝ), 0 < s → s < 1 / 2 →
    ∀ (a : SpatialCoordinates d → ℝ) (alpha : ℝ), 0 < alpha →
      ∀ (I P : Finset (Fin d)),
        Continuous a → (∀ x, 0 < a x) →
          ∀ (origData : SubdiffusiveProcess.CoarseGrainingVocab.ScalarTriadicCoeffData a)
            (foldData : SubdiffusiveProcess.CoarseGrainingVocab.ScalarTriadicCoeffData
              (fun x => a (coordinateFold 0 I P x))),
            SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError
                (Homogenization.originCube d 0) 0 s
                Homogenization.Book.Ch02.MultiscaleExponent.infinity
                (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
                foldData.toTriadicCoeffFamily alpha ≤
              ENNReal.ofReal (1 + 3 * (d : ℝ) /
                ((3 : ℝ) ^ (1 - 2 * s) - 1)) *
                SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError
                  (Homogenization.originCube d 0) 0 s
                  Homogenization.Book.Ch02.MultiscaleExponent.infinity
                  (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
                  origData.toTriadicCoeffFamily alpha := by
  intro d hd _ _ s hs hs1 a alpha halpha I P hcont hpos origData foldData
  let z : SpatialCoordinates d := 0
  let r : ℝ := (3 : ℝ) ^ (0 : ℕ)
  have hr : 0 < r := by
    dsimp [r]
    norm_num
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have : NeZero d := ⟨Nat.ne_of_gt hd0⟩
  have hD : ∀ J (k : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
      ∀ u : killedSobolevGraph (oddGridCell z r hr (triadicHalf J) k),
        ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) k)).1‖ ≤
          K * ‖subspaceGradient
            (killedSobolevGraph (oddGridCell z r hr (triadicHalf J) k)) u‖ := by
    intro J k
    have hdom : Homogenization.IsOpenBoundedConvexDomain
        (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d)) := by
      refine ⟨(oddGridCell z r hr (triadicHalf J) k).isOpen,
        (Homogenization.Bornology.IsBounded.isBoundedDomain
          (centeredCube_isBounded _ (div_pos hr (by positivity)))), ?_⟩
      change Convex ℝ (Metric.ball (oddGridCenter z r (triadicHalf J) k)
        ((r / (2 * (triadicHalf J : ℝ) + 1)) / 2))
      exact convex_ball _ _
    exact (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
      (oddGridCell z r hr (triadicHalf J) k) hdom).1
  have hN : ∀ J (k : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
      ∀ u : meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf J) k),
        ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) k)).1‖ ≤
          K * ‖subspaceGradient
            (meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf J) k)) u‖ := by
    intro J k
    have hdom : Homogenization.IsOpenBoundedConvexDomain
        (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d)) := by
      refine ⟨(oddGridCell z r hr (triadicHalf J) k).isOpen,
        (Homogenization.Bornology.IsBounded.isBoundedDomain
          (centeredCube_isBounded _ (div_pos hr (by positivity)))), ?_⟩
      change Convex ℝ (Metric.ball (oddGridCenter z r (triadicHalf J) k)
        ((r / (2 * (triadicHalf J : ℝ) + 1)) / 2))
      exact convex_ball _ _
    exact (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
      (oddGridCell z r hr (triadicHalf J) k) hdom).2
  have hseries :
      (∑' l : ℕ, ENNReal.ofReal (Homogenization.Book.Ch02.geometricWeight s 2 l) *
          SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale
            (Homogenization.originCube d (0 : ℤ)) ((0 : ℤ) - (l : ℤ))
            foldData.toTriadicCoeffFamily alpha) ≤
        ENNReal.ofReal (1 + 3 * (d : ℝ) /
          ((3 : ℝ) ^ (1 - 2 * s) - 1)) *
          ∑' l : ℕ, ENNReal.ofReal (Homogenization.Book.Ch02.geometricWeight s 2 l) *
            SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale
              (Homogenization.originCube d (0 : ℤ)) ((0 : ℤ) - (l : ℤ))
              origData.toTriadicCoeffFamily alpha := by
    refine _root_.SubdiffusiveProcess.Paper.folded_probe_discounted_le z hr hD hN hd0 0 hs hs1
      a alpha halpha I P hcont hpos (by rfl) (by norm_num [r])
      origData foldData ?_
    intro N k p
    dsimp
    intro J hdisj hcover
    have hI : (triadicObservationPlanes N I k).Nonempty :=
      triadicAdaptivePlanes_nonempty_of_ae_cover _ _ _ _ hcover
    have hrootdom : Homogenization.IsOpenBoundedConvexDomain
        (centeredCube (oddGridCenter z r (triadicHalf N) k)
          (r / (2 * (triadicHalf N : ℝ) + 1))
          (div_pos hr (by positivity)) : Set (SpatialCoordinates d)) := by
      refine ⟨(centeredCube _ _ _).isOpen,
        Homogenization.Bornology.IsBounded.isBoundedDomain
          (centeredCube_isBounded _ (div_pos hr (by positivity))), ?_⟩
      change Convex ℝ (Metric.ball (oddGridCenter z r (triadicHalf N) k)
        ((r / (2 * (triadicHalf N : ℝ) + 1)) / 2))
      exact convex_ball _ _
    have hD0 :=
      (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
        (centeredCube (oddGridCenter z r (triadicHalf N) k)
          (r / (2 * (triadicHalf N : ℝ) + 1))
          (div_pos hr (by positivity))) hrootdom).1
    have hN0 :=
      (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
        (centeredCube (oddGridCenter z r (triadicHalf N) k)
          (r / (2 * (triadicHalf N : ℝ) + 1))
          (div_pos hr (by positivity))) hrootdom).2
    constructor
    · exact triadicAdaptive_affineDirichletResponse_le_sum _ _ hI J
        hD0 (fun n l => observation_killedPoincare z hr hD N k n l) _ p
    · exact triadicAdaptive_affineInverseNeumannResponse_le_sum _ _ hI J
        hN0 (fun n l => observation_meanZeroPoincare z hr hN N k n l) _ p
  have hden : (0 : ℝ) < (3 : ℝ) ^ (1 - 2 * s) - 1 := by
    have hpow : (1 : ℝ) < (3 : ℝ) ^ (1 - 2 * s) :=
      (Real.one_lt_rpow_iff_of_pos (by norm_num)).2
        (Or.inl ⟨by norm_num, by linarith⟩)
    linarith
  have hc : (1 : ℝ) ≤ 1 + 3 * (d : ℝ) /
      ((3 : ℝ) ^ (1 - 2 * s) - 1) := by
    have hnonneg : (0 : ℝ) ≤ 3 * (d : ℝ) /
        ((3 : ℝ) ^ (1 - 2 * s) - 1) :=
      div_nonneg (by positivity) hden.le
    linarith
  rw [SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError_infinity_two_eq_weighted_series,
    SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError_infinity_two_eq_weighted_series]
  calc
    _ ≤ (ENNReal.ofReal (1 + 3 * (d : ℝ) /
        ((3 : ℝ) ^ (1 - 2 * s) - 1)) *
        (∑' l : ℕ, ENNReal.ofReal (Homogenization.Book.Ch02.geometricWeight s 2 l) *
          SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale
            (Homogenization.originCube d (0 : ℤ)) ((0 : ℤ) - (l : ℤ))
            origData.toTriadicCoeffFamily alpha)) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow hseries (by norm_num)
    _ = ENNReal.ofReal (1 + 3 * (d : ℝ) /
        ((3 : ℝ) ^ (1 - 2 * s) - 1)) ^ (1 / 2 : ℝ) *
        (∑' l : ℕ, ENNReal.ofReal (Homogenization.Book.Ch02.geometricWeight s 2 l) *
          SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale
            (Homogenization.originCube d (0 : ℤ)) ((0 : ℤ) - (l : ℤ))
            origData.toTriadicCoeffFamily alpha) ^ (1 / 2 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    _ ≤ ENNReal.ofReal (1 + 3 * (d : ℝ) /
        ((3 : ℝ) ^ (1 - 2 * s) - 1)) *
        (∑' l : ℕ, ENNReal.ofReal (Homogenization.Book.Ch02.geometricWeight s 2 l) *
          SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale
            (Homogenization.originCube d (0 : ℤ)) ((0 : ℤ) - (l : ℤ))
            origData.toTriadicCoeffFamily alpha) ^ (1 / 2 : ℝ) := by
      have hroot :
          ENNReal.ofReal (1 + 3 * (d : ℝ) /
            ((3 : ℝ) ^ (1 - 2 * s) - 1)) ^ (1 / 2 : ℝ) ≤
            ENNReal.ofReal (1 + 3 * (d : ℝ) /
              ((3 : ℝ) ^ (1 - 2 * s) - 1)) := by
        simpa only [ENNReal.rpow_one] using
          (ENNReal.rpow_le_rpow_of_exponent_le
            ((ENNReal.one_le_ofReal).2 hc) (by norm_num : (1 / 2 : ℝ) ≤ 1))
      exact mul_le_mul_left hroot _

end SubdiffusiveProcess.Paper
