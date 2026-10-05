module

public import SubdiffusiveProcess.Besov.GeometricTail
@[expose] public section

namespace SubdiffusiveProcess.Besov
open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov
open scoped BigOperators ENNReal
noncomputable section
variable {d : ℕ} [NeZero d]

private theorem rpow_natDepth_eq_pow (t : ℝ) (j : ℕ) :
    (3 : ℝ) ^ (-t * (j : ℝ)) = ((3 : ℝ) ^ (-t)) ^ j := by
  rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]

private theorem smallScale_multiscaleTerm_le (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) {m L₀ : ℤ} (hLm : L₀ ≤ m)
    {s : ℝ} (hs : 0 < s) {r : Ch02.MultiscaleExponent} (hr : r.IsAdmissible)
    (p q : Vec d) (i : ℕ) :
    (3 : ℝ) ^ (-((m - (L₀ - 1 - (i : ℤ)) : ℤ) : ℝ)) *
        Real.sqrt
          (descendantsAverage (originCube d m) (m - (L₀ - 1 - (i : ℤ))).toNat
            (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q)) ≤
      (Real.sqrt 2 *
            (Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
              maximizerEnergyL2Norm a ha (originCube d m) p q)) *
          ((3 : ℝ) ^ (-(1 - s))) ^ ((m - L₀).toNat + 1 + i) +
        (Real.sqrt 2 *
            Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) *
          ((3 : ℝ) ^ (-(1 : ℝ))) ^ ((m - L₀).toNat + 1 + i) := by
  have hidx : m - (L₀ - 1 - (i : ℤ)) = (((m - L₀).toNat + 1 + i : ℕ) : ℤ) := by
    have hK : ((m - L₀).toNat : ℤ) = m - L₀ := Int.toNat_of_nonneg (by omega)
    push_cast
    omega
  rw [hidx]
  simp only [Int.toNat_natCast, Int.cast_natCast]
  set j : ℕ := (m - L₀).toNat + 1 + i with hj
  set w : ℝ := (3 : ℝ) ^ (-((j : ℕ) : ℝ)) with hw
  have hw0 : 0 ≤ w := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
  have htri :=
    sqrt_descendantsAverage_parentCoarseScaleSeparationDeviationSq_le_energy a ha
      (originCube d m) j hs hr p q
  have hstep := mul_le_mul_of_nonneg_left htri hw0
  refine hstep.trans_eq ?_
  have hw1 :
      w * (3 : ℝ) ^ (s * (j : ℝ)) = (3 : ℝ) ^ (-(1 - s) * (j : ℝ)) :=
    rpow_neg_mul_rpow_mul s _
  have hw2 : w = (3 : ℝ) ^ (-(1 : ℝ) * (j : ℝ)) := by
    rw [hw]
    congr 1
    ring
  have hpow1 : (3 : ℝ) ^ (-(1 - s) * (j : ℝ)) = ((3 : ℝ) ^ (-(1 - s))) ^ j :=
    rpow_natDepth_eq_pow (1 - s) j
  have hpow2 : (3 : ℝ) ^ (-(1 : ℝ) * (j : ℝ)) = ((3 : ℝ) ^ (-(1 : ℝ))) ^ j :=
    rpow_natDepth_eq_pow 1 j
  calc
    w *
        (Real.sqrt 2 *
              ((3 : ℝ) ^ (s * (j : ℝ)) *
                Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
                maximizerEnergyL2Norm a ha (originCube d m) p q) +
            Real.sqrt 2 *
              Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q)))
        = (Real.sqrt 2 *
              (Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
                maximizerEnergyL2Norm a ha (originCube d m) p q)) *
              (w * (3 : ℝ) ^ (s * (j : ℝ))) +
            (Real.sqrt 2 *
              Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) * w := by
          ring
    _ = (Real.sqrt 2 *
              (Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
                maximizerEnergyL2Norm a ha (originCube d m) p q)) *
              ((3 : ℝ) ^ (-(1 - s))) ^ j +
            (Real.sqrt 2 *
              Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) *
              ((3 : ℝ) ^ (-(1 : ℝ))) ^ j := by
          rw [hw1, hpow1, hw2, hpow2]

/-- The small-scale tail on the full paper range `0 < s < 1`. -/
theorem sum_range_smallScale_multiscaleTerm_le_full (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) {m L₀ : ℤ} (hLm : L₀ ≤ m)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {r : Ch02.MultiscaleExponent} (hr : r.IsAdmissible) (p q : Vec d) (N : ℕ) :
    (∑ i ∈ Finset.range N,
        (3 : ℝ) ^ (-((m - (L₀ - 1 - (i : ℤ)) : ℤ) : ℝ)) *
          Real.sqrt (descendantsAverage (originCube d m) (m - (L₀ - 1 - (i : ℤ))).toNat
            (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q))) ≤
      (2 * Real.sqrt 2 / (1 - s)) *
          ((3 : ℝ) ^ (-(1 - s) * ((m - L₀ : ℤ) : ℝ)) *
            Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
            maximizerEnergyL2Norm a ha (originCube d m) p q) +
        2 * Real.sqrt 2 *
          ((3 : ℝ) ^ (-((m - L₀ : ℤ) : ℝ)) *
            Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) := by
  have hK : (((m - L₀).toNat : ℕ) : ℤ) = m - L₀ := Int.toNat_of_nonneg (by omega)
  have hKR : (((m - L₀).toNat : ℕ) : ℝ) = ((m - L₀ : ℤ) : ℝ) := by exact_mod_cast hK
  let C₁ : ℝ := Real.sqrt 2 *
    (Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
      maximizerEnergyL2Norm a ha (originCube d m) p q)
  let C₂ : ℝ := Real.sqrt 2 *
    Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))
  have hC₁0 : 0 ≤ C₁ :=
    mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
      (maximizerEnergyL2Norm_nonneg a ha (originCube d m) p q))
  have hC₂0 : 0 ≤ C₂ := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hval1 : ((3 : ℝ) ^ (-(1 - s))) ^ ((m - L₀).toNat) =
      (3 : ℝ) ^ (-(1 - s) * ((m - L₀ : ℤ) : ℝ)) := by
    rw [← rpow_natDepth_eq_pow (1 - s) ((m - L₀).toNat), hKR]
  have hval2 : ((3 : ℝ) ^ (-(1 : ℝ))) ^ ((m - L₀).toNat) =
      (3 : ℝ) ^ (-((m - L₀ : ℤ) : ℝ)) := by
    rw [← rpow_natDepth_eq_pow 1 ((m - L₀).toNat), hKR]
    congr 1
    ring
  calc
    _ ≤ ∑ i ∈ Finset.range N,
        (C₁ * ((3 : ℝ) ^ (-(1 - s))) ^ ((m - L₀).toNat + 1 + i) +
          C₂ * ((3 : ℝ) ^ (-(1 : ℝ))) ^ ((m - L₀).toNat + 1 + i)) :=
      Finset.sum_le_sum (fun i _ => smallScale_multiscaleTerm_le a ha hLm hs hr p q i)
    _ = C₁ * (∑ i ∈ Finset.range N,
          ((3 : ℝ) ^ (-(1 - s))) ^ ((m - L₀).toNat + 1 + i)) +
        C₂ * (∑ i ∈ Finset.range N,
          ((3 : ℝ) ^ (-(1 : ℝ))) ^ ((m - L₀).toNat + 1 + i)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ C₁ * ((2 / (1 - s)) * ((3 : ℝ) ^ (-(1 - s))) ^ ((m - L₀).toNat)) +
        C₂ * (2 * ((3 : ℝ) ^ (-(1 : ℝ))) ^ ((m - L₀).toNat)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (sum_range_discount_shift_le (by linarith) _ N) hC₁0)
        (mul_le_mul_of_nonneg_left (by simpa only [div_one] using (sum_range_discount_shift_le
          (by norm_num : (0 : ℝ) < 1) (m - L₀).toNat N)) hC₂0)
    _ = _ := by
      rw [hval1, hval2]
      dsimp [C₁, C₂]
      ring

end
end SubdiffusiveProcess.Besov
