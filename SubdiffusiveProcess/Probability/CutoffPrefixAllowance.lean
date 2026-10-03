module

public import SubdiffusiveProcess.Probability.PrefixMeshAllowance
public import SubdiffusiveProcess.Analysis.CutoffPrefixBudget

@[expose] public section

/-! A common prefix allowance for all cutoffs. A shallow transfer handles
covered prefixes; the original exponential tails handle the remaining ones.
The complement must have a linear cutoff bound in root depth and length.
This module does not supply model-specific prefix estimates or geometry.
-/
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Topology
namespace SubdiffusiveProcess

/-- Union over a linear number of cutoffs consumes at most half the exponential rate. -/
theorem cutoff_prefix_union_tail
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (bad : ℕ → Set Omega) (A c xi : ℝ) (buffer m : ℕ)
    (hA : 0 < A) (hc : 0 ≤ c) (hxi : 0 < xi)
    (htail : ∀ N, mu (bad N) ≤ ENNReal.ofReal (Real.exp (-(2 * A * m)))) :
    mu (⋃ N : Fin (⌈(c * (xi⁻¹ + 1 + buffer) + 1) * ((m : ℝ) + 1)⌉₊ + 1),
      bad N.val) ≤
      ENNReal.ofReal ((c * (xi⁻¹ + 1 + buffer) + 3) * (1 + A⁻¹) *
        Real.exp (-(A * m))) := by
  let L := ⌈(c * (xi⁻¹ + 1 + buffer) + 1) * ((m : ℝ) + 1)⌉₊
  have hK : 0 ≤ c * (xi⁻¹ + 1 + buffer) + 3 := by positivity
  calc mu (⋃ N : Fin (L + 1), bad N.val) ≤ ∑ N : Fin (L + 1), mu (bad N.val) :=
      measure_iUnion_fintype_le mu _
    _ ≤ ∑ _N : Fin (L + 1), ENNReal.ofReal (Real.exp (-(2 * A * m))) :=
      Finset.sum_le_sum (fun N _ => htail N.val)
    _ = ENNReal.ofReal (((L : ℝ) + 1) * Real.exp (-(2 * A * m))) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (by positivity)]
      simp only [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one,
        ENNReal.ofReal_natCast, ENNReal.ofReal_one, Nat.cast_add, Nat.cast_one]
    _ ≤ ENNReal.ofReal ((c * (xi⁻¹ + 1 + buffer) + 3) *
        (((m : ℝ) + 1) * Real.exp (-(2 * A * m)))) := by
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_right
        (cutoff_prefix_budget_card_le c xi buffer m hc hxi) (Real.exp_pos (-(2 * A * m))).le
      simpa only [L, mul_assoc] using hh
    _ ≤ ENNReal.ofReal ((c * (xi⁻¹ + 1 + buffer) + 3) * (1 + A⁻¹) *
        Real.exp (-(A * m))) := by
      apply ENNReal.ofReal_le_ofReal
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (linear_mul_exp_double_le A m hA (Nat.cast_nonneg _)) hK

/-- A shallow prefix transfer and original tails give one affine allowance for every cutoff. -/
theorem ae_all_cutoff_prefix_allowance
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (k : ℕ → ℕ) (d b buffer : ℕ) (Ccount A xi c : ℝ)
    (hCcount : 0 ≤ Ccount) (hA : 0 < A) (hxi : 0 < xi) (hc : 0 ≤ c)
    (hrate : (d : ℝ) * Real.log 3 < A * xi)
    (hcard : ∀ n : ℕ, (k n : ℝ) ≤
      Ccount * ((n : ℝ) + 1) ^ b * (3 : ℝ) ^ ((d : ℝ) * n))
    (bad : ∀ N n : ℕ, Fin (k n) → ℕ → Set Omega)
    (htail : ∀ N n i m, 1 ≤ m →
      mu (bad N n i m) ≤ ENNReal.ofReal (Real.exp (-(2 * A * m))))
    (covered : ℕ → ℕ → ℕ → Prop)
    (hcomplement : ∀ N n m, ¬ covered N n m →
      (N : ℝ) ≤ c * ((n : ℝ) + m + buffer))
    (hshort : ∀ᵐ omega ∂mu, ∃ B : ℝ, 0 < B ∧
      ∀ᶠ N : ℕ in atTop, ∀ (n : ℕ) (i : Fin (k n)) (m : ℕ), xi * (n : ℝ) + B ≤ (m : ℝ) →
        covered N n m → omega ∉ bad N n i m) :
    ∀ᵐ omega ∂mu, ∃ B : ℝ, 0 < B ∧
      ∀ (N n : ℕ) (i : Fin (k n)) (m : ℕ),
        xi * (n : ℝ) + B ≤ (m : ℝ) → omega ∉ bad N n i m := by
  classical
  let L := fun m : ℕ => ⌈(c * (xi⁻¹ + 1 + buffer) + 1) * ((m : ℝ) + 1)⌉₊
  let event := fun n (i : Fin (k n)) (m : ℕ) =>
    if 1 ≤ m ∧ xi * (n : ℝ) ≤ m then ⋃ N : Fin (L m + 1), bad N.val n i m else ∅
  let Ctail := (c * (xi⁻¹ + 1 + buffer) + 3) * (1 + A⁻¹)
  have hCtail : 0 ≤ Ctail := by dsimp only [Ctail]; positivity
  have hevent n i m : mu (event n i m) ≤ ENNReal.ofReal (Ctail * Real.exp (-(A * m))) := by
    by_cases h : 1 ≤ m ∧ xi * (n : ℝ) ≤ m
    · simp only [event, if_pos h]
      exact cutoff_prefix_union_tail mu (fun N => bad N n i m) A c xi buffer m
        hA hc hxi (fun N => htail N n i m h.1)
    · simp only [event, if_neg h, measure_empty]
      exact zero_le
  have hlong := exists_common_prefix_allowance mu k d b Ccount Ctail A xi
    hCcount hCtail hA hxi hrate hcard
    (fun n i m => toMeasurable mu (event n i m))
    (fun n i m => measurableSet_toMeasurable mu (event n i m))
    (fun n i m => by rw [measure_toMeasurable]; simpa only [neg_mul] using hevent n i m)
  filter_upwards [hshort, hlong] with omega hS hL
  obtain ⟨Bs, hBs, hS⟩ := hS
  obtain ⟨Bl, hBl, hL⟩ := hL
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hS
  let B := max Bs (max Bl ((N0 : ℝ) + 1))
  have hBsB : Bs ≤ B := le_max_left _ _
  have hBlB : Bl ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hNB : (N0 : ℝ) + 1 ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨B, hBs.trans_le hBsB, ?_⟩
  intro N n i m hlen
  have hxn := mul_nonneg hxi.le (Nat.cast_nonneg (α := ℝ) n)
  have hm1 : 1 ≤ m := by
    have hmpos : (0 : ℝ) < m := by linarith only [hlen, hBs, hBsB, hxn]
    exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast ne_of_gt hmpos)
  have hdepth : xi * (n : ℝ) ≤ m := by linarith only [hlen, hBs, hBsB]
  have hcond : 1 ≤ m ∧ xi * (n : ℝ) ≤ m := ⟨hm1, hdepth⟩
  by_cases hcovered : covered N n m
  · by_cases hN : N0 ≤ N
    · exact hN0 N hN n i m (by linarith only [hlen, hBsB]) hcovered
    · have hNm : N ≤ m := by
        have hmN : (N0 : ℝ) ≤ m := by linarith only [hlen, hNB, hxn]
        have hN0m : N0 ≤ m := by exact_mod_cast hmN
        omega
      have hNL := hNm.trans (cutoff_prefix_budget_ge_length c xi buffer m hc hxi)
      change N ≤ L m at hNL
      intro hbad
      apply hL n i m (by linarith only [hlen, hBlB])
      apply subset_toMeasurable mu (event n i m)
      simp only [event, if_pos hcond, mem_iUnion]
      exact ⟨⟨N, by omega⟩, hbad⟩
  · have hNL := cutoff_prefix_budget_covers c xi buffer n m N hc hxi hdepth
      (hcomplement N n m hcovered)
    change N ≤ L m at hNL
    intro hbad
    apply hL n i m (by linarith only [hlen, hBlB])
    apply subset_toMeasurable mu (event n i m)
    simp only [event, if_pos hcond, mem_iUnion]
    exact ⟨⟨N, by omega⟩, hbad⟩

end SubdiffusiveProcess
