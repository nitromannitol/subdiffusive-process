import SubdiffusiveProcess.Besov.SpatialPairing

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
open scoped BigOperators ENNReal
noncomputable section
namespace SubdiffusiveProcess.Besov

/-- One scale entry of the weak negative norm. -/
def negativeEntry {d : ℕ} (m : ℤ) (s : ℝ) (r : ℝ≥0∞) (f : Vec d → ℝ) (n : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal ((3 : ℝ) ^ ((n : ℝ) * s)) *
    averageLr (negativeCentres d m n) r
      (fun z => ENNReal.ofReal |⨍ x in translatedCube d n z, f x|)

/-- One scale entry of the positive local-L1 norm. -/
def positiveEntry {d : ℕ} (m : ℤ) (s : ℝ) (r : ℝ≥0∞) (g : Vec d → ℝ) (n : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ) * s)) *
    averageLr (positiveCentres d m n) r
      (fun z => normalizedLp (translatedCube d n z) 1
        (fun x => g x - ⨍ y in translatedCube d n z, g y))

/-- The two adjacent-scale weights cancel up to 3^s. -/
theorem adjacent_scale_weights (m : ℤ) (j : ℕ) (s : ℝ) :
    ENNReal.ofReal ((3 : ℝ) ^ s) *
      (ENNReal.ofReal ((3 : ℝ) ^ (((m - (j + 1) : ℤ) : ℝ) * s)) *
        ENNReal.ofReal ((3 : ℝ) ^ (-((m - j : ℤ) : ℝ) * s))) = 1 := by
  rw [← ENNReal.ofReal_mul (Real.rpow_pos_of_pos (by norm_num) _).le,
    ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos (by norm_num) _).le,
    ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
  have he : s + (((m - (j + 1) : ℤ) : ℝ) * s + -((m - j : ℤ) : ℝ) * s) = 0 := by
    push_cast
    ring
  rw [he, Real.rpow_zero, ENNReal.ofReal_one]

private theorem weighted_product_identity (K a b c w v : ℝ≥0∞) (hw : c * (w * v) = 1) :
    K * K * (a * b) = c * K * K * ((w * a) * (v * b)) := by
  calc
    _ = 1 * (K * K * (a * b)) := (one_mul _).symm
    _ = (c * (w * v)) * (K * K * (a * b)) := congrArg (fun t => t * _) hw.symm
    _ = _ := by ac_rfl

/-- A pairing increment is bounded by the product of its two weighted entries. -/
theorem pairing_increment_le_entries {d : ℕ} (m : ℤ) (j : ℕ)
    (s : ℝ) (hsOne : s ≤ 1) (r : ℝ≥0∞) (hr : 1 ≤ r) (f g : Vec d → ℝ)
    (hg : IntegrableOn g (cubeSet (originCube d m))) :
    ENNReal.ofReal |cubeAverage (originCube d m)
      (fun x => cubeProjection (originCube d m) (j + 1) f x *
        cubeProjectionResidual (originCube d m) j g x)| ≤
      (3 : ℝ≥0∞) * (3 ^ d : ℕ) * (3 ^ d : ℕ) *
        (negativeEntry m s r f (m - (j + 1)) *
          positiveEntry m s (ENNReal.conjExponent r) g (m - j)) := by
  have h3 : ENNReal.ofReal ((3 : ℝ) ^ s) ≤ 3 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hsOne
    simpa using ENNReal.ofReal_le_ofReal h
  have hsp := spatial_pairing_le_averages m j r hr f g hg
  unfold negativeEntry positiveEntry
  calc
    _ ≤ _ := hsp
    _ = ENNReal.ofReal ((3 : ℝ) ^ s) * (3 ^ d : ℕ) * (3 ^ d : ℕ) *
        ((ENNReal.ofReal ((3 : ℝ) ^ (((m - (j + 1) : ℤ) : ℝ) * s)) *
          averageLr (negativeCentres d m (m - (j + 1))) r
            (fun z => ENNReal.ofReal |⨍ x in translatedCube d (m - (j + 1)) z, f x|)) *
        (ENNReal.ofReal ((3 : ℝ) ^ (-((m - j : ℤ) : ℝ) * s)) *
          averageLr (positiveCentres d m (m - j)) (ENNReal.conjExponent r)
            (fun z => normalizedLp (translatedCube d (m - j) z) 1
              (fun x => g x - ⨍ y in translatedCube d (m - j) z, g y)))) := by
      exact weighted_product_identity _ _ _ _ _ _ (adjacent_scale_weights m j s)
    _ ≤ _ := by gcongr

/-- Scale Holder controls all finite telescope increments, including the endpoints. -/
theorem pairing_increment_sum_le {d : ℕ} (m : ℤ) (N : ℕ) (s : ℝ)
    (hs : 0 < s) (hsOne : s ≤ 1) (q r : ℝ≥0∞) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (f g : Vec d → ℝ) (hg : IntegrableOn g (cubeSet (originCube d m))) :
    (∑ j ∈ Finset.range N, ENNReal.ofReal |cubeAverage (originCube d m)
      (fun x => cubeProjection (originCube d m) (j + 1) f x *
        cubeProjectionResidual (originCube d m) j g x)|) ≤
      (3 : ℝ≥0∞) * (3 ^ d : ℕ) * (3 ^ d : ℕ) * ENNReal.ofReal s⁻¹ *
        (negativeBesovNorm d m s r q f *
          besovSeminorm d m s 1 (ENNReal.conjExponent q) (ENNReal.conjExponent r) g) := by
  have hsum := Finset.sum_le_sum (s := Finset.range N) (fun j _ =>
    pairing_increment_le_entries m j s hsOne r hr f g hg)
  rw [← Finset.mul_sum] at hsum
  have hscale := scaleAggregation_holder_reindexed (Finset.range N) s hs m q hq
    (negativeEntry m s r f) (positiveEntry m s (ENNReal.conjExponent r) g)
    (fun j => m - (j + 1)) (fun j => m - j)
    (by intro a _ b _ h; dsimp only at h; omega) (by intro a _ b _ h; dsimp only at h; omega)
    (by intro j _; dsimp only; omega) (by intro j _; dsimp only; omega)
  exact hsum.trans ((mul_le_mul_right hscale _).trans_eq (by
    unfold negativeBesovNorm besovSeminorm negativeEntry positiveEntry
    ac_rfl))

end SubdiffusiveProcess.Besov
