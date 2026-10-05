module

public import SubdiffusiveProcess.Main.OriginalGridResponseConvolution
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.CubeNegativeL2Norm
public import SubdiffusiveProcess.Main.HalfFractionalOrder
public import SubdiffusiveProcess.Sobolev.BoundaryEnergy
public import SubdiffusiveProcess.Sobolev.FoldDiscounts
public import SubdiffusiveProcess.Sobolev.LoadApproximation
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.CoarseGrainingVocab.Core
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecayInterior.InteriorHarmonic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowsAboveCutoff
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.UncutGammaOneTail
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.GoodScaleSaturation
public import SubdiffusiveProcess.Frozen.Section6.HarmonicApproximationGoodScalesInterior
public import SubdiffusiveProcess.Frozen.Section6.Defs.GoodEvent
public import SubdiffusiveProcess.Frozen.Section6.Defs.AccumulatedError
public import SubdiffusiveProcess.Frozen.Section6.Defs.HolderRegularityConclusions
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_J

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

attribute [local instance] Classical.propDecidable



structure in_iteration (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (E : in_J d)
    (S : in_6_16 d M) where
  good : ℕ → SpatialCoordinates d → ℝ → ℝ → BilateralField d → Prop
  good_eq : ∀ (j : ℕ) (z : SpatialCoordinates d) (eps s : ℝ) (omega : BilateralField d),
    good j z eps s omega ↔
      ∃ xi : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        (∀ (i : ℕ) (x : SpatialCoordinates d), xi i x = omega (i : ℤ) x) ∧
        xi ∈ SubdiffusiveProcess.CoarseGrainingVocab.goodEvent M none j z eps s
  score : ℕ → SpatialCoordinates d → ℝ → BilateralField d → ℝ
  score_eq : ∀ (j : ℕ) (z : SpatialCoordinates d) (s : ℝ) (omega : BilateralField d),
    score j z s omega =
      sSup {v : ℝ |
        ∃ xi : _root_.SubdiffusiveProcess.Model.PotentialSample d,
          (∀ (i : ℕ) (x : SpatialCoordinates d), xi i x = omega (i : ℤ) x) ∧
          v = SubdiffusiveProcess.CoarseGrainingVocab.accumulatedError M none j z s xi}
  score_nonneg : ∀ j z s0' om, 0 ≤ score j z s0' om
  ref : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ
  ref_pos : ∀ L j z om, 0 < ref L j z om
  ref_eq : ∀ (L j : ℕ) (z : SpatialCoordinates d) (omega : BilateralField d),
    ref L j z omega = S.refAvg L (j + 2) z omega
  C0 : ℝ
  C0_pos : 0 < C0
  C0_eq : ∀ inst : NeZero d,
    letI := inst
    let H := SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_interiorRowsAboveCutoff d
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecayInterior.interiorHolderExcessDecayInput_of_interiorHarmonic
        d (fun [NeZero d] => SubdiffusiveProcess.Frozen.Section6.harmonic_approximation_good_scales_interior d))
    let c1 := Classical.choose H
    let c2 := Classical.choose (Classical.choose_spec H)
    let cmin := Classical.choose (Classical.choose_spec (Classical.choose_spec H))
    C0 = max (max 46 c1) (max (1024 * c2 ^ 2) cmin)
  C : ℝ
  C_pos : 0 < C
  C_eq : ∀ inst : NeZero d,
    letI := inst
    let H := SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_interiorRowsAboveCutoff d
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecayInterior.interiorHolderExcessDecayInput_of_interiorHarmonic
        d (fun [NeZero d] => SubdiffusiveProcess.Frozen.Section6.harmonic_approximation_good_scales_interior d))
    let c1 := Classical.choose H
    let c2 := Classical.choose (Classical.choose_spec H)
    let cmin := Classical.choose (Classical.choose_spec (Classical.choose_spec H))
    let c0 := max (max 46 c1) (max (1024 * c2 ^ 2) cmin)
    let hH := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec H))
    let h1 : (1 : ℝ) ≤ c1 := le_trans (by norm_num) hH.1
    let h2 : (1 : ℝ) ≤ c2 := le_trans h1 hH.2.1
    let Ct := Classical.choose
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_uncutGammaOneTail d 21 h1 h2)
    let Ce := Classical.choose
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.exists_section6HomogenizationError_le_cutoff_min_of_scale_le_cutoff d)
    C = max S.C (max c0 (max Ct Ce))
  C_ge_one : 1 ≤ C
  C1 : ℝ
  C1_pos : 0 < C1
  C1_eq : ∀ inst : NeZero d,
    letI := inst
    let H := SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_interiorRowsAboveCutoff d
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecayInterior.interiorHolderExcessDecayInput_of_interiorHarmonic
        d (fun [NeZero d] => SubdiffusiveProcess.Frozen.Section6.harmonic_approximation_good_scales_interior d))
    let c1 := Classical.choose H
    let _c2 := Classical.choose (Classical.choose_spec H)
    let _cmin := Classical.choose (Classical.choose_spec (Classical.choose_spec H))
    C1 = c1
  C2 : ℝ
  C2_pos : 0 < C2
  C2_eq : ∀ inst : NeZero d,
    letI := inst
    let H := SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.exists_interiorRowsAboveCutoff d
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecayInterior.interiorHolderExcessDecayInput_of_interiorHarmonic
        d (fun [NeZero d] => SubdiffusiveProcess.Frozen.Section6.harmonic_approximation_good_scales_interior d))
    let _c1 := Classical.choose H
    let c2 := Classical.choose (Classical.choose_spec H)
    let _cmin := Classical.choose (Classical.choose_spec (Classical.choose_spec H))
    C2 = c2
  C1_C2_le_one : C1 * C2 ^ (-8 : ℝ) ≤ 1
  k : ℕ
  k_eq : k = 21
  s0 : ℝ
  s0_eq : s0 = 1 / 32
  theta : ℝ
  theta_eq : theta = (3 : ℝ) ^ (-(1 / 4) : ℝ)
  alphaRange : Set ℝ
  alphaRange_eq : alphaRange =
    Set.Icc (1 / 2 : ℝ) (1 - C * M.delta * Real.sqrt |Real.log M.delta|)
  good_error : ∀ (L j : ℕ) (z : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ (j + 2))
      (eps : ℝ) (om : BilateralField d),
      64 * M.delta ^ 2 ≤ s0 → s0 ≤ 1 / 2 → s0⁻¹ * M.delta ^ 2 ≤ eps → eps ≤ 1 →
      good (j + 2) z eps s0 om → j + 2 ≤ L →
      E.err z ((3 : ℝ) ^ (j + 2)) hR (S.cutoffOn L om z ((3 : ℝ) ^ (j + 2)) hR) z
          ((3 : ℝ) ^ (j + 2)) (ref L j z om) s0 2 ≤
        C * min eps (s0⁻¹ * M.delta ^ 2 + eps ^ 8 + score (j + 2) z s0 om)
  prefixLen : SpatialCoordinates d → ℝ → ℕ → BilateralField d → ℕ
  prefix_measurable : ∀ (z : SpatialCoordinates d) (alpha : ℝ) (m : ℕ),
    Measurable (prefixLen z alpha m)
  prefix_lower : ∀ (z : SpatialCoordinates d) (alpha : ℝ) (m : ℕ) (omega : BilateralField d),
    k + 5 ≤ prefixLen z alpha m omega
  prefix_tail : ∀ (z : SpatialCoordinates d) (alpha : ℝ), alpha ∈ alphaRange →
    M.delta ≤ C⁻¹ → ∀ (m k' : ℕ),
    (chaosSampleLaw M).toMeasure {om | k' < prefixLen z alpha m om} ≤
      ENNReal.ofReal (C * Real.exp (-((1 - alpha) ^ 2 * (max ((k' : ℝ) - C) 0) /
        (C * M.delta ^ 2 * |Real.log M.delta|))))
  good_scale_sums : ∀ (z : SpatialCoordinates d) (alpha : ℝ), alpha ∈ alphaRange →
      M.delta ≤ C⁻¹ →
      ∀ (lam eps : ℝ), lam = C1⁻¹ * (1 - alpha) →
      eps = C2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ) →
      ∀ (n m : ℕ) (om : BilateralField d),
      (n : ℤ) ≤ (m : ℤ) - prefixLen z alpha m om →
      (∑ j ∈ Finset.Icc n m, score j z s0 om) ≤ lam * ((m : ℝ) - n) ∧
      (((Finset.Icc n m).filter (fun j => ¬ good j z eps s0 om)).card : ℝ) <
        1 + lam * ((m : ℝ) - n)
  badSet : SpatialCoordinates d → ℝ → ℕ → ℕ → BilateralField d → Finset ℕ
  badSet_eq : ∀ (z : SpatialCoordinates d) (alpha : ℝ) (n m : ℕ) (omega : BilateralField d),
    badSet z alpha n m omega =
      (Finset.Icc n m).filter (fun j =>
        j + 2 ≤ m ∧
          (j < n + k ∨ ¬ good (j + 2) z (C2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ)) s0 omega))
  bad_count : ∀ (z : SpatialCoordinates d) (alpha : ℝ), alpha ∈ alphaRange →
      M.delta ≤ C⁻¹ →
      ∀ (lam : ℝ), lam = C1⁻¹ * (1 - alpha) →
      ∀ (n m : ℕ) (om : BilateralField d),
      (n : ℤ) ≤ (m : ℤ) - prefixLen z alpha m om →
      ((badSet z alpha n m om).card : ℝ) ≤ (k : ℝ) + 1 + lam * ((m : ℝ) - n)
  stepError : ℕ → SpatialCoordinates d → ℝ → BilateralField d → ℝ
  stepError_eq : ∀ (j : ℕ) (z : SpatialCoordinates d) (eps : ℝ) (omega : BilateralField d),
    stepError j z eps omega =
      C * s0 ^ (-(3 / 2 : ℝ)) *
          min eps (M.delta ^ 2 + eps ^ 8 + score (j + 2) z s0 omega) *
        (if good (j + 2) z eps s0 omega then 1 else 0)
  Csum : ℝ
  Csum_pos : 0 < Csum
  Csum_eq : Csum = 3 * C * s0^(-(3/2 : Real))
  error_sum : ∀ (z : SpatialCoordinates d) (alpha : ℝ), alpha ∈ alphaRange →
      M.delta ≤ C⁻¹ →
      ∀ (lam eps : ℝ), lam = C1⁻¹ * (1 - alpha) →
      eps = C2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ) →
      ∀ (n m : ℕ) (om : BilateralField d),
      (n : ℤ) ≤ (m : ℤ) - prefixLen z alpha m om →
      (∑ j ∈ (Finset.Icc n m).filter (fun j => j + 2 ≤ m), stepError j z eps om) ≤
        C * s0 ^ (-(3 / 2 : ℝ)) *
          ((M.delta ^ 2 + eps ^ 8) * ((m : ℝ) - n) +
            ∑ j ∈ (Finset.Icc n m).filter (fun j => j + 2 ≤ m), score (j + 2) z s0 om) ∧
      C * s0 ^ (-(3 / 2 : ℝ)) *
          ((M.delta ^ 2 + eps ^ 8) * ((m : ℝ) - n) +
            ∑ j ∈ (Finset.Icc n m).filter (fun j => j + 2 ≤ m), score (j + 2) z s0 om) ≤
        Csum * lam * ((m : ℝ) - n)
  ref_ratio : ∀ (L : ℕ) (z : SpatialCoordinates d) (alpha : ℝ), alpha ∈ alphaRange →
      M.delta ≤ C⁻¹ →
      ∀ (lam : ℝ), lam = C1⁻¹ * (1 - alpha) →
      ∀ (n m j : ℕ) (om : BilateralField d),
      (n : ℤ) ≤ (m : ℤ) - prefixLen z alpha m om →
      m ≤ L → n ≤ j → j + 5 ≤ m →
      C⁻¹ * Real.exp (-(C * lam * ((m : ℝ) - n))) ≤
          ref L j z om / ref L (m - 2) z om ∧
        ref L j z om / ref L (m - 2) z om ≤ C * Real.exp (C * lam * ((m : ℝ) - n))

end SubdiffusiveProcess.Paper
