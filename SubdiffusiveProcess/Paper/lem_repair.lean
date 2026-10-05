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
public import SubdiffusiveProcess.Frozen.Section6.Defs.GoodEvent
public import SubdiffusiveProcess.Frozen.Section6.Defs.HolderRegularityConclusions
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.lem_repair_err_fold_localization
public import SubdiffusiveProcess.Paper.lem_repair_err_good_scale_transport
public import SubdiffusiveProcess.Paper.lem_repair_err_sum_transport

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

attribute [local instance] Classical.propDecidable

/-- lemma  (paper label `eq:mfd-11`): reference identification and the full
discounted coarse error after folding.  One declaration, no auxiliaries; the metadata and
the manuscript correspondence are owned by the general.

Suppliers and conclusions, tick list:
- pointwise folding bound from `cor_fold` (paper `eq:mfd-11`), with the exact dimensional
      constant `Cd = sqrt(1 + 3d/(3^{1-2s0}-1))`;
- original error bound from `in_iteration.good_error`, the second
      pointwise inequality `Cd * original E.err <= Cc * min eps (... + D_j)`;
- original references from `in_6_16`/`in_responses` (`refAvg`, `refScalar`) as the
      defining-identity ties of the reference scalar;
- original finite bad set and counts/ratios from `in_iteration` (`badSet`, `bad_count`,
      `ref_ratio`);
- fixed `s0 = It.s0` and the paper's admissible `epsilon` (`64 delta^2 <= s0`,
      `s0^-1 delta^2 <= eps`, `eps <= 1`), not a free `s0` interval;
- common original objects and scalar-law ties, on the actual working-subcube `E.err`;
- finite true complement `I \ 𝓑_z` of the bad set, membership not hypothesized;
- full discounted error: both pointwise inequalities and the summed display;
- constant order `Cc`: chosen from dimension alone before model/input structures (the source generic constant may enlarge);
- the proof below combines these inputs into the displayed folding estimates.

The folding or accumulated-error conclusion is never added as a hypothesis. -/
theorem lem_repair :
  ∀ (d : ℕ) (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)],
  ∃ Cc : ℝ, 0 < Cc ∧
    ∀ (E : in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (Rm : in_responses d M) (Sreg : in_6_16 d M)
      (It : in_iteration d M E Sreg),
    ∀ (alpha : ℝ), alpha ∈ It.alphaRange → M.delta ≤ It.C⁻¹ →
    let s0 : ℝ := It.s0;
    let eps : ℝ := It.C2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ);
    let lam : ℝ := It.C1⁻¹ * (1 - alpha);
    64 * M.delta ^ 2 ≤ s0 → s0⁻¹ * M.delta ^ 2 ≤ eps → eps ≤ 1 →
    ∀ (L m : ℕ) (z : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ m)
      (om : BilateralField d) (I P : Finset (Fin d)),
      I.Nonempty →
      ∀ foldedCoef : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ m) hR),
        ((foldedCoef.val : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))]
          fun x => (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR).val
            (coordinateFold z I P x)) →
        (∀ j : ℕ, j + 2 ≤ L → j + 2 ≤ m → It.good (j + 2) z eps s0 om →
          E.err z ((3 : ℝ) ^ m) hR foldedCoef z ((3 : ℝ) ^ (j + 2))
              (It.ref L j z om) s0 2 ≤
            Real.sqrt (1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * s0) - 1)) *
              E.err z ((3 : ℝ) ^ m) hR (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR) z
                ((3 : ℝ) ^ (j + 2)) (It.ref L j z om) s0 2 ∧
          Real.sqrt (1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * s0) - 1)) *
              E.err z ((3 : ℝ) ^ m) hR (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR) z
                ((3 : ℝ) ^ (j + 2)) (It.ref L j z om) s0 2 ≤
            Cc * min eps (M.delta ^ 2 + eps ^ 8 + It.score (j + 2) z s0 om)) ∧
        (∀ n : ℕ, n + 2 ≤ m → m ≤ L →
          (∑ j ∈ (Finset.Ico n (m - 1)) \ It.badSet z alpha n m om,
              E.err z ((3 : ℝ) ^ m) hR foldedCoef z ((3 : ℝ) ^ (j + 2))
                (It.ref L j z om) s0 2) ≤
            Cc * ((M.delta ^ 2 + eps ^ 8) * ((m : ℝ) - 1 - n) +
              ∑ j ∈ Finset.Ico n (m - 1), It.score (j + 2) z s0 om)) ∧
        (∀ j : ℕ,
          It.ref L j z om = Sreg.refAvg L (j + 2) z om ∧
          It.ref L j z om = Rm.refScalar L j z om) ∧
        (∀ n : ℕ, (n : ℤ) ≤ (m : ℤ) - It.prefixLen z alpha m om → m ≤ L →
          ((It.badSet z alpha n m om).card : ℝ) ≤
              (It.k : ℝ) + 1 + lam * ((m : ℝ) - n) ∧
          ∀ j : ℕ, n ≤ j → j + 5 ≤ m →
            It.C⁻¹ * Real.exp (-(It.C * lam * ((m : ℝ) - n))) ≤
                It.ref L j z om / It.ref L (m - 2) z om ∧
              It.ref L j z om / It.ref L (m - 2) z om ≤
                It.C * Real.exp (It.C * lam * ((m : ℝ) - n))) := by
  intro d hd hms hbs
  obtain ⟨Cg, hCg, hgood⟩ := @lem_repair_err_good_scale_transport d hd hms hbs
  obtain ⟨Cs, hCs, hsum⟩ := @lem_repair_err_sum_transport d hd hms hbs
  refine ⟨max Cg Cs, lt_of_lt_of_le hCg (le_max_left Cg Cs), ?_⟩
  intro E M Rm Sreg It alpha halpha hdelta s0 eps lam h64 hse heps L m z hR om I P hI foldedCoef hfold
  have hfold_loc :=
    @lem_repair_err_fold_localization d hd hms hbs E M Sreg It alpha halpha hdelta h64 hse heps
      L m z hR om I P hI foldedCoef hfold
  have hb1 := hgood E M Sreg It alpha halpha hdelta h64 hse heps
  have hb2 := hsum E M Sreg It alpha halpha hdelta h64 hse heps
  have hs0 : 0 < s0 := by
    simpa using (show 0 < It.s0 from by rw [It.s0_eq]; norm_num)
  have hnonneg_ref : 0 ≤ s0⁻¹ * M.delta ^ 2 := by positivity
  have heps0 : 0 ≤ eps := le_trans hnonneg_ref hse
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hjL hjm hgj
    refine ⟨hfold_loc j hjL hjm hgj, ?_⟩
    have hb := hb1 L m j z hR om hjL hjm hgj
    refine le_trans hb ?_
    refine mul_le_mul_of_nonneg_right (le_max_left Cg Cs) ?_
    refine le_min ?_ ?_
    · exact le_trans (by positivity) hse
    · exact add_nonneg (add_nonneg (sq_nonneg M.delta) (by positivity))
        (It.score_nonneg (j + 2) z s0 om)
  · intro n hn hm
    have hb := hb2 L m z hR om I P hI foldedCoef hfold n hn hm
    refine le_trans hb ?_
    refine mul_le_mul_of_nonneg_right (le_max_right Cg Cs) ?_
    refine add_nonneg ?_ ?_
    · refine mul_nonneg (add_nonneg (sq_nonneg M.delta) (by positivity)) ?_
      have hcast : (n : ℝ) + 2 ≤ (m : ℝ) := by exact_mod_cast hn
      linarith
    · exact Finset.sum_nonneg (fun j _ => It.score_nonneg (j + 2) z s0 om)
  · intro j
    constructor
    · exact It.ref_eq L j z om
    · calc
        It.ref L j z om = Sreg.refAvg L (j + 2) z om := It.ref_eq L j z om
        _ = Rm.refScalar L j z om := by
          have hjR : (0 : ℝ) < 3 ^ (j + 2) := by positivity
          rw [Sreg.refAvg_eq L (j + 2) z om hjR, Rm.refScalar_eq L j z om hjR]
          congr 1
          apply integral_congr_ae
          filter_upwards [] with x
          rw [Rm.bRef_eq, Rm.coeffScalar_eq, Rm.coeffScalar_eq]
          rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
          congr 1
          congr 1
          rw [Nat.cast_min]
          ring
  · intro n hn hm
    refine ⟨It.bad_count z alpha halpha hdelta lam rfl n m om hn, ?_⟩
    intro j hj hjm
    exact It.ref_ratio L z alpha halpha hdelta lam rfl n m j om hn hm hj hjm

end SubdiffusiveProcess.Paper
