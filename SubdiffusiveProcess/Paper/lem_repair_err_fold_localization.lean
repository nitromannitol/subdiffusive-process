module

public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.OriginalGridResponseConvolution
public import SubdiffusiveProcess.Sobolev.FoldDiscounts
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.CoarseGrainingVocab.Core
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
public import SubdiffusiveProcess.Section6.Defs.GoodEvent
public import SubdiffusiveProcess.Section6.Defs.HolderRegularityConclusions
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowFiniteSideConditions
public import SubdiffusiveProcess.Paper.cor_fold
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.folded_probe_discounted_le
public import SubdiffusiveProcess.Paper.lem_repair_err_fold_carrier_bridge
public import SubdiffusiveProcess.Paper.lem_repair_err_fold_paper_comparison

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

attribute [local instance] Classical.propDecidable

theorem aux_lem_repair_err_fold_localization_series :
  ∀ (d : ℕ) (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)],
  ∀ (s : ℝ), 0 < s → s < 1 / 2 →
    ∀ (a : SpatialCoordinates d → ℝ) (alpha : ℝ), 0 < alpha →
      ∀ (I P : Finset (Fin d)),
        Continuous a → (∀ x, 0 < a x) →
          ∀ (origData : SubdiffusiveProcess.CoarseGrainingVocab.ScalarTriadicCoeffData a)
            (foldData : SubdiffusiveProcess.CoarseGrainingVocab.ScalarTriadicCoeffData
              (fun x => a (coordinateFold 0 I P x))),
            (∑' l : ℕ, ENNReal.ofReal (Homogenization.Book.Ch02.geometricWeight s 2 l) *
                SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale
                  (Homogenization.originCube d (0 : ℤ)) ((0 : ℤ) - (l : ℤ))
                  foldData.toTriadicCoeffFamily alpha) ≤
              ENNReal.ofReal (1 + 3 * (d : ℝ) /
                ((3 : ℝ) ^ (1 - 2 * s) - 1)) *
                ∑' l : ℕ, ENNReal.ofReal
                    (Homogenization.Book.Ch02.geometricWeight s 2 l) *
                  SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale
                    (Homogenization.originCube d (0 : ℤ)) ((0 : ℤ) - (l : ℤ))
                    origData.toTriadicCoeffFamily alpha := by
  intro d hd _ _ s hs hs1 a alpha halpha I P hcont hpos origData foldData
  let z : SpatialCoordinates d := 0
  let r : ℝ := (3 : ℝ) ^ (0 : ℕ)
  have hr : 0 < r := by
    dsimp [r]
    norm_num
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  let : NeZero d := ⟨by omega⟩
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



theorem lem_repair_err_fold_localization :
  ∀ (d : ℕ) (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)],
  ∀ (E : in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg),
    ∀ (alpha : ℝ), alpha ∈ It.alphaRange → M.delta ≤ It.C⁻¹ →
    let s0 : ℝ := It.s0
    let eps : ℝ := It.C2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ)
    64 * M.delta ^ 2 ≤ s0 → s0⁻¹ * M.delta ^ 2 ≤ eps → eps ≤ 1 →
    ∀ (L m : ℕ) (z : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ m)
      (om : BilateralField d) (I P : Finset (Fin d)),
      I.Nonempty →
      ∀ foldedCoef : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ m) hR),
        ((foldedCoef.val : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))]
          fun x => (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR).val
            (coordinateFold z I P x)) →
        ∀ j : ℕ, j + 2 ≤ L → j + 2 ≤ m → It.good (j + 2) z eps s0 om →
          E.err z ((3 : ℝ) ^ m) hR foldedCoef z ((3 : ℝ) ^ (j + 2))
              (It.ref L j z om) s0 2 ≤
            Real.sqrt (1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * s0) - 1)) *
              E.err z ((3 : ℝ) ^ m) hR (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR) z
                ((3 : ℝ) ^ (j + 2)) (It.ref L j z om) s0 2 := by
  intro d hd hms hbs E M Sreg It alpha halpha hdelta
  dsimp only
  intro h64 hse heps L m z hR om I P hI foldedCoef hfolded j hjL hjm hgood
  have h_bridge :=
    lem_repair_err_fold_carrier_bridge d hd E M Sreg It L m z hR om I P hI
      foldedCoef hfolded j hjL hjm
  obtain ⟨a, ha, ha_pos, origData, foldData, herr_fold_eq, herr_orig_eq⟩ := h_bridge
  have hs0_pos : 0 < It.s0 := by rw [It.s0_eq]; norm_num
  have hs0_lt : It.s0 < 1 / 2 := by rw [It.s0_eq]; norm_num
  have href : 0 < It.ref L j z om := It.ref_pos L j z om
  have h_fold_ne_top :
      SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError (Homogenization.originCube d 0) 0 It.s0
        Homogenization.Book.Ch02.MultiscaleExponent.infinity
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
        foldData.toTriadicCoeffFamily (It.ref L j z om) ≠ ⊤ := by
    let : NeZero d := ⟨by omega⟩
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.fluxRowFinite_paperHomogenizationError_two_ne_top
      (Homogenization.originCube d 0) (by rfl) hs0_pos
      foldData.toTriadicCoeffFamily
      (fun Q => (foldData.onCube Q).isSymmetric) href
  have h_orig_ne_top :
      SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError (Homogenization.originCube d 0) 0 It.s0
        Homogenization.Book.Ch02.MultiscaleExponent.infinity
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
        origData.toTriadicCoeffFamily (It.ref L j z om) ≠ ⊤ := by
    let : NeZero d := ⟨by omega⟩
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.fluxRowFinite_paperHomogenizationError_two_ne_top
      (Homogenization.originCube d 0) (by rfl) hs0_pos
      origData.toTriadicCoeffFamily
      (fun Q => (origData.onCube Q).isSymmetric) href
  have hden : (0 : ℝ) < (3 : ℝ) ^ (1 - 2 * It.s0) - 1 := by
    have hpow : (1 : ℝ) < (3 : ℝ) ^ (1 - 2 * It.s0) :=
      (Real.one_lt_rpow_iff_of_pos (by norm_num)).2
        (Or.inl ⟨by norm_num, by linarith⟩)
    linarith
  have hCnonneg : (0 : ℝ) ≤ 1 + 3 * (d : ℝ) /
      ((3 : ℝ) ^ (1 - 2 * It.s0) - 1) := by
    have hnonneg : (0 : ℝ) ≤ 3 * (d : ℝ) /
        ((3 : ℝ) ^ (1 - 2 * It.s0) - 1) :=
      div_nonneg (by positivity) hden.le
    linarith
  let A : ℝ≥0∞ := ∑' l : ℕ, ENNReal.ofReal
      (Homogenization.Book.Ch02.geometricWeight It.s0 2 l) *
    SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale
      (Homogenization.originCube d (0 : ℤ)) ((0 : ℤ) - (l : ℤ))
      foldData.toTriadicCoeffFamily (It.ref L j z om)
  let B : ℝ≥0∞ := ∑' l : ℕ, ENNReal.ofReal
      (Homogenization.Book.Ch02.geometricWeight It.s0 2 l) *
    SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale
      (Homogenization.originCube d (0 : ℤ)) ((0 : ℤ) - (l : ℤ))
      origData.toTriadicCoeffFamily (It.ref L j z om)
  have hseries : A ≤ ENNReal.ofReal (1 + 3 * (d : ℝ) /
      ((3 : ℝ) ^ (1 - 2 * It.s0) - 1)) * B := by
    simpa [A, B] using
      (aux_lem_repair_err_fold_localization_series d hd It.s0 hs0_pos
        hs0_lt a (It.ref L j z om) href I P ha ha_pos origData foldData)
  have hB_ne_top : B ≠ ⊤ := by
    intro hB
    apply h_orig_ne_top
    rw [SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError_infinity_two_eq_weighted_series]
    change B ^ (1 / 2 : ℝ) = ⊤
    rw [hB]
    exact ENNReal.top_rpow_of_pos (by norm_num)
  have hseries_rpow := ENNReal.rpow_le_rpow hseries
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hseries_rpow_real := ENNReal.toReal_mono
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB_ne_top)) hseries_rpow
  have hfold_eq :
      SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError (Homogenization.originCube d 0) 0 It.s0
        Homogenization.Book.Ch02.MultiscaleExponent.infinity
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
        foldData.toTriadicCoeffFamily (It.ref L j z om) = A ^ (1 / 2 : ℝ) := by
    rw [SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError_infinity_two_eq_weighted_series]
  have horig_eq :
      SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError (Homogenization.originCube d 0) 0 It.s0
        Homogenization.Book.Ch02.MultiscaleExponent.infinity
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
        origData.toTriadicCoeffFamily (It.ref L j z om) = B ^ (1 / 2 : ℝ) := by
    rw [SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError_infinity_two_eq_weighted_series]
  have h_real_paper :
      (SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError (Homogenization.originCube d 0) 0 It.s0
        Homogenization.Book.Ch02.MultiscaleExponent.infinity
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
        foldData.toTriadicCoeffFamily (It.ref L j z om)).toReal ≤
      Real.sqrt (1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * It.s0) - 1)) *
        (SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError (Homogenization.originCube d 0) 0 It.s0
          Homogenization.Book.Ch02.MultiscaleExponent.infinity
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
          origData.toTriadicCoeffFamily (It.ref L j z om)).toReal := by
    rw [hfold_eq, horig_eq]
    calc
      (A ^ (1 / 2 : ℝ)).toReal ≤
          ((ENNReal.ofReal (1 + 3 * (d : ℝ) /
            ((3 : ℝ) ^ (1 - 2 * It.s0) - 1)) * B) ^
              (1 / 2 : ℝ)).toReal := hseries_rpow_real
      _ = Real.sqrt (1 + 3 * (d : ℝ) /
            ((3 : ℝ) ^ (1 - 2 * It.s0) - 1)) *
          (B ^ (1 / 2 : ℝ)).toReal := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.toReal_mul,
          ENNReal.ofReal_rpow_of_nonneg hCnonneg (by norm_num),
          ENNReal.toReal_ofReal (Real.rpow_nonneg hCnonneg (1 / 2 : ℝ)),
          Real.sqrt_eq_rpow]
  rw [herr_fold_eq, herr_orig_eq]
  exact h_real_paper

end SubdiffusiveProcess.Paper
