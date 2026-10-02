import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.CoarseGrainingVocab.Core
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
import SubdiffusiveProcess.Frozen.Section6.Defs.GoodEvent
import SubdiffusiveProcess.Frozen.Section6.Defs.HolderRegularityConclusions
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.lem_repair_err_fold_localization
import SubdiffusiveProcess.Paper.lem_repair_err_good_scale_transport

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

attribute [local instance] Classical.propDecidable



theorem lem_repair_err_sum_transport :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)],
  ∃ Cs : ℝ, 0 < Cs ∧
    ∀ (E : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
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
              =ᵐ[volume.restrict
                (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))]
            fun x => (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR).val
              (coordinateFold z I P x)) →
          ∀ n : ℕ, n + 2 ≤ m → m ≤ L →
            (∑ j ∈ (Finset.Ico n (m - 1)) \ It.badSet z alpha n m om,
                E.err z ((3 : ℝ) ^ m) hR foldedCoef z ((3 : ℝ) ^ (j + 2))
                  (It.ref L j z om) s0 2) ≤
      Cs * ((M.delta ^ 2 + eps ^ 8) * ((m : ℝ) - 1 - n) +
                ∑ j ∈ Finset.Ico n (m - 1), It.score (j + 2) z s0 om) := by
  intro d hd _ _
  obtain ⟨Cg, hCgpos, hCg⟩ := lem_repair_err_good_scale_transport (d := d) hd
  refine ⟨Cg, hCgpos, ?_⟩
  intro E M Sreg It alpha halpha hdelta s0 eps h64 hratio heps
  intro L m z hR om I P hI foldedCoef hfold n hnm hmL
  let T : Finset ℕ := Finset.Ico n (m - 1)
  let D : Finset ℕ := T \ It.badSet z alpha n m om
  let A : ℝ := M.delta ^ 2 + eps ^ 8
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hcard : (T.card : ℝ) = (m : ℝ) - 1 - n := by
    dsimp [T]
    rw [Nat.card_Ico]
    rw [Nat.cast_sub (by omega : n ≤ m - 1)]
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    norm_num
  have hsum_bound :
      (∑ j ∈ D, (A + It.score (j + 2) z s0 om)) ≤
        A * ((m : ℝ) - 1 - n) +
          ∑ j ∈ T, It.score (j + 2) z s0 om := by
    have hconst : (∑ j ∈ D, A) ≤ ∑ j ∈ T, A := by
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        (fun _ _ _ => hA)
    have hscore :
        (∑ j ∈ D, It.score (j + 2) z s0 om) ≤
          ∑ j ∈ T, It.score (j + 2) z s0 om := by
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        (fun j _ _ => It.score_nonneg (j + 2) z s0 om)
    calc
      (∑ j ∈ D, (A + It.score (j + 2) z s0 om)) =
          (∑ j ∈ D, A) + ∑ j ∈ D, It.score (j + 2) z s0 om := by
            rw [Finset.sum_add_distrib]
      _ ≤ (∑ j ∈ T, A) + ∑ j ∈ T, It.score (j + 2) z s0 om :=
        add_le_add hconst hscore
      _ = A * ((m : ℝ) - 1 - n) +
          ∑ j ∈ T, It.score (j + 2) z s0 om := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        ring
  calc
    (∑ j ∈ (Finset.Ico n (m - 1)) \ It.badSet z alpha n m om,
        E.err z ((3 : ℝ) ^ m) hR foldedCoef z ((3 : ℝ) ^ (j + 2))
          (It.ref L j z om) s0 2) =
        ∑ j ∈ D, E.err z ((3 : ℝ) ^ m) hR foldedCoef z ((3 : ℝ) ^ (j + 2))
          (It.ref L j z om) s0 2 := by rfl
    _ ≤ ∑ j ∈ D, (Cg * (A + It.score (j + 2) z s0 om)) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hjT, hjbad⟩ := Finset.mem_sdiff.mp hj
      obtain ⟨hjn, hjupper⟩ := Finset.mem_Ico.mp (by simpa [T] using hjT)
      have hjm : j + 2 ≤ m := by omega
      have hjL : j + 2 ≤ L := by omega
      have hgood : It.good (j + 2) z eps s0 om := by
        by_contra hng
        apply hjbad
        rw [It.badSet_eq]
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · rw [Finset.mem_Icc]
          omega
        · exact ⟨hjm, Or.inr hng⟩
      have hfl := lem_repair_err_fold_localization d hd E M Sreg It alpha
        halpha hdelta h64 hratio heps L m z hR om I P hI foldedCoef hfold
        j hjL hjm hgood
      have htr := hCg E M Sreg It alpha halpha hdelta h64 hratio heps
        L m j z hR om hjL hjm hgood
      calc
        E.err z ((3 : ℝ) ^ m) hR foldedCoef z ((3 : ℝ) ^ (j + 2))
              (It.ref L j z om) s0 2 ≤
            Real.sqrt (1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * s0) - 1)) *
              E.err z ((3 : ℝ) ^ m) hR
                (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR) z
                ((3 : ℝ) ^ (j + 2)) (It.ref L j z om) s0 2 := hfl
        _ ≤ Cg * min eps (M.delta ^ 2 + eps ^ 8 +
              It.score (j + 2) z s0 om) := htr
        _ ≤ Cg * (A + It.score (j + 2) z s0 om) := by
          apply mul_le_mul_of_nonneg_left
          · exact min_le_right _ _
          · exact le_of_lt hCgpos
        _ = Cg * (A + It.score (j + 2) z s0 om) := by rfl
    _ = Cg * (∑ j ∈ D, (A + It.score (j + 2) z s0 om)) := by
      rw [Finset.mul_sum]
    _ ≤ Cg * (A * ((m : ℝ) - 1 - n) +
        ∑ j ∈ T, It.score (j + 2) z s0 om) := by
      exact mul_le_mul_of_nonneg_left hsum_bound (le_of_lt hCgpos)
    _ = Cg * ((M.delta ^ 2 + eps ^ 8) * ((m : ℝ) - 1 - n) +
        ∑ j ∈ Finset.Ico n (m - 1), It.score (j + 2) z s0 om) := by
      simp only [A, T]

end Paper

