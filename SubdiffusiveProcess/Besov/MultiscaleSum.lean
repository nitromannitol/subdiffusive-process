module

public import SubdiffusiveProcess.Besov.SmallScaleTail
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov.JBoundByBesov
@[expose] public section

namespace SubdiffusiveProcess.Besov
open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov
open Homogenization.Book.Ch05.Section53
open scoped BigOperators ENNReal
noncomputable section
variable {d : ℕ} [NeZero d]

private theorem rpow_neg_natCast_eq_inv_pow (j : ℕ) :
    (3 : ℝ) ^ (-(j : ℝ)) = ((3 : ℝ) ^ j)⁻¹ := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]

/-! ## Splitting the depth range at the base scale -/

private theorem sum_range_le_head_add_tail (K N : ℕ) (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j) :
    ∑ j ∈ Finset.range (N + 2), T j ≤
      (∑ j ∈ Finset.range (K + 1), T j) + ∑ i ∈ Finset.range (N + 2), T (K + 1 + i) := by
  classical
  set B : Finset ℕ := (Finset.range (N + 2)).image (fun i => K + 1 + i) with hB
  have hsub : Finset.range (N + 2) ⊆ Finset.range (K + 1) ∪ B := by
    intro j hj
    simp only [Finset.mem_range] at hj
    by_cases hjk : j < K + 1
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr hjk)
    · refine Finset.mem_union_right _ ?_
      refine Finset.mem_image.mpr ⟨j - (K + 1), Finset.mem_range.mpr (by omega), by omega⟩
  have h1 : ∑ j ∈ Finset.range (N + 2), T j ≤ ∑ j ∈ Finset.range (K + 1) ∪ B, T j :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hT j
  have h2 : (∑ j ∈ Finset.range (K + 1) ∪ B, T j) +
      ∑ j ∈ Finset.range (K + 1) ∩ B, T j =
      (∑ j ∈ Finset.range (K + 1), T j) + ∑ j ∈ B, T j :=
    Finset.sum_union_inter
  have h3 : 0 ≤ ∑ j ∈ Finset.range (K + 1) ∩ B, T j :=
    Finset.sum_nonneg fun j _ => hT j
  have h4 : ∑ j ∈ B, T j = ∑ i ∈ Finset.range (N + 2), T (K + 1 + i) := by
    rw [hB]
    exact Finset.sum_image fun x _ y _ hxy => by omega
  linarith

/-! ## Reindexing the two ranges -/

omit [NeZero d] in
/-- The head of the depth range is the manuscript sum over `n \in [L_0,m]`. -/
private theorem sum_range_head_eq_sum_Icc (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) {m L₀ : ℤ} (hLm : L₀ ≤ m) (p q : Vec d) :
    ∑ j ∈ Finset.range ((m - L₀).toNat + 1),
        ((3 : ℝ) ^ j)⁻¹ *
          Real.sqrt (descendantsAverage (originCube d m) j
            (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q)) =
      ∑ n ∈ Finset.Icc L₀ m,
        (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
          Real.sqrt (descendantsAverage (originCube d m) (m - n).toNat
            (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q)) := by
  refine Finset.sum_nbij' (fun j : ℕ => m - (j : ℤ)) (fun n : ℤ => (m - n).toNat) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_range] at hj
    simp only [Finset.mem_Icc]
    omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    simp only [Finset.mem_range]
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    show (m - (m - (j : ℤ))).toNat = j
    omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    show m - (((m - n).toNat : ℕ) : ℤ) = n
    omega
  · intro j _
    have hj2 : m - (m - (j : ℤ)) = (j : ℤ) := by ring
    rw [hj2, Int.toNat_natCast, Int.cast_natCast, rpow_neg_natCast_eq_inv_pow]

omit [NeZero d] in
/-- The tail of the depth range is the manuscript sum over `n < L_0`. -/
private theorem sum_range_tail_eq (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) {m L₀ : ℤ} (hLm : L₀ ≤ m) (p q : Vec d)
    (M : ℕ) :
    ∑ i ∈ Finset.range M,
        ((3 : ℝ) ^ ((m - L₀).toNat + 1 + i))⁻¹ *
          Real.sqrt (descendantsAverage (originCube d m) ((m - L₀).toNat + 1 + i)
            (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q)) =
      ∑ i ∈ Finset.range M,
        (3 : ℝ) ^ (-((m - (L₀ - 1 - (i : ℤ)) : ℤ) : ℝ)) *
          Real.sqrt (descendantsAverage (originCube d m) (m - (L₀ - 1 - (i : ℤ))).toNat
            (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q)) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have hK : ((m - L₀).toNat : ℤ) = m - L₀ := Int.toNat_of_nonneg (by omega)
  have hidx : m - (L₀ - 1 - (i : ℤ)) = (((m - L₀).toNat + 1 + i : ℕ) : ℤ) := by
    push_cast
    omega
  rw [hidx, Int.toNat_natCast, Int.cast_natCast, rpow_neg_natCast_eq_inv_pow]

/-! ## The four-term bound at every depth cutoff -/

/-- **The four printed right-hand terms bound every partial multiscale sum.**
The head of the depth range is discharged by the summed large-scale display and
the tail by the small-scale tail, on the identical summand.
It is public because the `l.J.bound.by.Besov` assembly bounds its own partial
multiscale sums by the same four terms. -/
theorem sum_range_multiscaleTerm_le_fourTerm_full (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) {m L₀ : ℤ} (hLm : L₀ ≤ m)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {r : Ch02.MultiscaleExponent} (hr : r.IsAdmissible) (p q : Vec d) (N : ℕ) :
    ∑ j ∈ Finset.range (N + 2),
        ((3 : ℝ) ^ j)⁻¹ *
          Real.sqrt (descendantsAverage (originCube d m) j
            (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q)) ≤
      2 * Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
            (∑ n ∈ Finset.Icc L₀ m,
              (3 : ℝ) ^ (-(1 - s) * ((m - n : ℤ) : ℝ)) *
                Real.sqrt (WeakNormsMaximizer.responseDefectAverageAtScale m n p q a)) +
          Real.sqrt 2 *
            (∑ n ∈ Finset.Icc L₀ m,
              (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
                Real.sqrt (descendantsAverage (originCube d m) (m - n).toNat
                  (coarseMatrixVariationSq a ha (originCube d m) p q))) +
          (2 * Real.sqrt 2 / (1 - s)) *
            ((3 : ℝ) ^ (-(1 - s) * ((m - L₀ : ℤ) : ℝ)) *
              Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
              maximizerEnergyL2Norm a ha (originCube d m) p q) +
          2 * Real.sqrt 2 *
            ((3 : ℝ) ^ (-((m - L₀ : ℤ) : ℝ)) *
              Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) := by
  have hT : ∀ j : ℕ,
      0 ≤ ((3 : ℝ) ^ j)⁻¹ *
        Real.sqrt (descendantsAverage (originCube d m) j
          (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q)) := by
    intro j
    positivity
  have hP3 :=
    sum_Icc_weighted_sqrt_descendantsAverage_parentCoarseScaleSeparationDeviationSq_le
      a ha m L₀ hs hr p q
  have hP4 := sum_range_smallScale_multiscaleTerm_le_full a ha hLm hs hs1 hr p q (N + 2)
  calc
    ∑ j ∈ Finset.range (N + 2),
        ((3 : ℝ) ^ j)⁻¹ *
          Real.sqrt (descendantsAverage (originCube d m) j
            (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q))
        ≤ (∑ j ∈ Finset.range ((m - L₀).toNat + 1),
              ((3 : ℝ) ^ j)⁻¹ *
                Real.sqrt (descendantsAverage (originCube d m) j
                  (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q))) +
            ∑ i ∈ Finset.range (N + 2),
              ((3 : ℝ) ^ ((m - L₀).toNat + 1 + i))⁻¹ *
                Real.sqrt (descendantsAverage (originCube d m) ((m - L₀).toNat + 1 + i)
                  (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q)) :=
          sum_range_le_head_add_tail ((m - L₀).toNat) N _ hT
    _ = (∑ n ∈ Finset.Icc L₀ m,
              (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
                Real.sqrt (descendantsAverage (originCube d m) (m - n).toNat
                  (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q))) +
            ∑ i ∈ Finset.range (N + 2),
              (3 : ℝ) ^ (-((m - (L₀ - 1 - (i : ℤ)) : ℤ) : ℝ)) *
                Real.sqrt (descendantsAverage (originCube d m) (m - (L₀ - 1 - (i : ℤ))).toNat
                  (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q)) := by
          rw [sum_range_head_eq_sum_Icc a ha hLm p q, sum_range_tail_eq a ha hLm p q (N + 2)]
    _ ≤ (2 * Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
              (∑ n ∈ Finset.Icc L₀ m,
                (3 : ℝ) ^ (-(1 - s) * ((m - n : ℤ) : ℝ)) *
                  Real.sqrt (WeakNormsMaximizer.responseDefectAverageAtScale m n p q a)) +
            Real.sqrt 2 *
              ∑ n ∈ Finset.Icc L₀ m,
                (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
                  Real.sqrt (descendantsAverage (originCube d m) (m - n).toNat
                    (coarseMatrixVariationSq a ha (originCube d m) p q))) +
            ((2 * Real.sqrt 2 / (1 - s)) *
                ((3 : ℝ) ^ (-(1 - s) * ((m - L₀ : ℤ) : ℝ)) *
                  Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
                  maximizerEnergyL2Norm a ha (originCube d m) p q) +
              2 * Real.sqrt 2 *
                ((3 : ℝ) ^ (-((m - L₀ : ℤ) : ℝ)) *
                  Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q)))) :=
          add_le_add hP3 hP4
    _ = _ := by ring

theorem partialMultiscaleSum_le_fourTerm_full (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) {m L₀ : ℤ} (hLm : L₀ ≤ m)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {r : Ch02.MultiscaleExponent} (hr : r.IsAdmissible) (p q : Vec d) (K : ℕ) :
    ∑ j ∈ Finset.range K,
        ((3 : ℝ) ^ j)⁻¹ *
          Real.sqrt (descendantsAverage (originCube d m) j
            (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q)) ≤
      2 * Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
            (∑ n ∈ Finset.Icc L₀ m,
              (3 : ℝ) ^ (-(1 - s) * ((m - n : ℤ) : ℝ)) *
                Real.sqrt (WeakNormsMaximizer.responseDefectAverageAtScale m n p q a)) +
          Real.sqrt 2 *
            (∑ n ∈ Finset.Icc L₀ m,
              (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
                Real.sqrt (descendantsAverage (originCube d m) (m - n).toNat
                  (coarseMatrixVariationSq a ha (originCube d m) p q))) +
          (2 * Real.sqrt 2 / (1 - s)) *
            ((3 : ℝ) ^ (-(1 - s) * ((m - L₀ : ℤ) : ℝ)) *
              Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
              maximizerEnergyL2Norm a ha (originCube d m) p q) +
          2 * Real.sqrt 2 *
            ((3 : ℝ) ^ (-((m - L₀ : ℤ) : ℝ)) *
              Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) := by
  have hsub : Finset.range K ⊆ Finset.range (K + 2) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) ?_
  · intro j _ _
    positivity
  · exact sum_range_multiscaleTerm_le_fourTerm_full a ha hLm hs hs1 hr p q K

theorem centredMultiscaleAverageSum_le_fourTerm_full (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) {m L₀ : ℤ} (hLm : L₀ ≤ m)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {r : Ch02.MultiscaleExponent} (hr : r.IsAdmissible) (p q : Vec d) :
    centredMultiscaleAverageSum a ha m p q ≤
      2 * Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
            (∑ n ∈ Finset.Icc L₀ m,
              (3 : ℝ) ^ (-(1 - s) * ((m - n : ℤ) : ℝ)) *
                Real.sqrt (WeakNormsMaximizer.responseDefectAverageAtScale m n p q a)) +
          Real.sqrt 2 *
            (∑ n ∈ Finset.Icc L₀ m,
              (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
                Real.sqrt (descendantsAverage (originCube d m) (m - n).toNat
                  (coarseMatrixVariationSq a ha (originCube d m) p q))) +
          (2 * Real.sqrt 2 / (1 - s)) *
            ((3 : ℝ) ^ (-(1 - s) * ((m - L₀ : ℤ) : ℝ)) *
              Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
              maximizerEnergyL2Norm a ha (originCube d m) p q) +
          2 * Real.sqrt 2 *
            ((3 : ℝ) ^ (-((m - L₀ : ℤ) : ℝ)) *
              Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) :=
  ciSup_le fun N => partialMultiscaleSum_le_fourTerm_full a ha hLm hs hs1 hr p q N


end
end SubdiffusiveProcess.Besov
