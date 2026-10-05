module

public import SubdiffusiveProcess.Besov.PairingScaleBounds

@[expose] public section

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
open scoped BigOperators ENNReal
noncomputable section
namespace SubdiffusiveProcess.Besov

/-- A dimensional constant for the finite pairing bound. -/
def pairingConstant (d : ℕ) : ℝ := 3 * (3 ^ d : ℕ) * (3 ^ d : ℕ) + 1

theorem pairingConstant_pos (d : ℕ) : 0 < pairingConstant d := by
  unfold pairingConstant
  positivity

/-- The top-scale mean contribution in the positive norm. -/
def rootEntry {d : ℕ} (m : ℤ) (s : ℝ) (g : Vec d → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((3 : ℝ) ^ (-(m : ℝ) * s)) *
    ENNReal.ofReal |cubeAverage (originCube d m) g|

theorem besovNorm_eq_seminorm_add_root {d : ℕ} (m : ℤ) (s : ℝ)
    (p q r : ℝ≥0∞) (g : Vec d → ℝ) :
    besovNorm d m s p q r g = besovSeminorm d m s p q r g + rootEntry m s g := by
  unfold besovNorm rootEntry
  rw [cube, openCube_average_eq, ENNReal.ofReal_mul (Real.rpow_pos_of_pos (by norm_num) _).le]

/-- At the root there is exactly one negative-norm averaging centre. -/
theorem negative_average_root {d : ℕ} (m : ℤ) (r : ℝ≥0∞) (hr : 1 ≤ r) (f : Vec d → ℝ) :
    averageLr (negativeCentres d m m) r
      (fun z => ENNReal.ofReal |⨍ x in translatedCube d m z, f x|) =
      ENNReal.ofReal |cubeAverage (originCube d m) f| := by
  have h := negative_average_eq_depthAggregation m 0 r f
  simpa [depthAggregation, finiteAggregation_singleton_one _ r hr] using h

/-- The top negative entry controls the product of the two root means. -/
theorem root_pairing_le {d : ℕ} (m : ℤ) (s : ℝ) (hs : 0 < s) (hsOne : s ≤ 1)
    (q r : ℝ≥0∞) (hq : 1 ≤ q) (hr : 1 ≤ r) (f g : Vec d → ℝ) :
    ENNReal.ofReal |cubeAverage (originCube d m) f * cubeAverage (originCube d m) g| ≤
      ENNReal.ofReal s⁻¹ *
        (rootEntry m s g * negativeBesovNorm d m s r q f) := by
  have hneg := scaleAggregation_entry_le s hs hsOne m m le_rfl q hq (negativeEntry m s r f)
  change negativeEntry m s r f m ≤ ENNReal.ofReal s⁻¹ * negativeBesovNorm d m s r q f at hneg
  have hw : ENNReal.ofReal ((3 : ℝ) ^ (-(m : ℝ) * s)) *
      ENNReal.ofReal ((3 : ℝ) ^ ((m : ℝ) * s)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_pos_of_pos (by norm_num) _).le,
      ← Real.rpow_add (by norm_num)]
    have he : -(m : ℝ) * s + (m : ℝ) * s = 0 := by ring
    rw [he, Real.rpow_zero, ENNReal.ofReal_one]
  have heq : rootEntry m s g * negativeEntry m s r f m =
      ENNReal.ofReal |cubeAverage (originCube d m) f * cubeAverage (originCube d m) g| := by
    unfold rootEntry negativeEntry
    rw [negative_average_root m r hr, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
    calc
      _ = (ENNReal.ofReal ((3 : ℝ) ^ (-(m : ℝ) * s)) *
          ENNReal.ofReal ((3 : ℝ) ^ ((m : ℝ) * s))) *
          (ENNReal.ofReal |cubeAverage (originCube d m) f| *
            ENNReal.ofReal |cubeAverage (originCube d m) g|) := by ac_rfl
      _ = _ := by rw [hw, one_mul]
  rw [← heq]
  exact (mul_le_mul_right hneg (rootEntry m s g)).trans_eq (by ac_rfl)

/-- The existing projection telescope only needs local L1 integrability. -/
theorem pairing_projection_telescope {d : ℕ} (Q : TriadicCube d) (N : ℕ) (f g : Vec d → ℝ)
    (hf : IntegrableOn f (cubeSet Q)) (hg : IntegrableOn g (cubeSet Q)) :
    cubeBesovPairing Q f (cubeProjection Q N g) =
      cubeAverage Q f * cubeAverage Q g + ∑ j ∈ Finset.range N,
        cubeAverage Q (fun x => cubeProjection Q (j + 1) f x * cubeProjectionResidual Q j g x) := by
  have ht := cubeBesovPairing_projection_eq_cubeAverage_mul_cubeAverage_add_sum Q 1 g f N hf
    (by intro j _ R hR
        exact fluctuation_memLp_one R (hg.mono_set (cubeSet_subset_of_mem_descendantsAtDepth hR)))
    (by intro j _ R hR
        simpa [cubeBesovConjExponent, ENNReal.conjExponent] using
          cubeProjection_succ_memLp_of_mem_descendantsAtDepth ⊤ f hR) le_rfl
  have hc : cubeBesovPairing Q f (cubeProjection Q N g) =
      cubeBesovPairing Q g (cubeProjection Q N f) := by
    rw [← cubeBesovPairing_projection_comm Q N f g hf hg]
    unfold cubeBesovPairing
    congr 1
    funext x
    exact mul_comm _ _
  rw [hc, ht, mul_comm (cubeAverage Q g)]

private theorem absorb_root_and_sum (K t u v F : ℝ≥0∞) :
    t * (u * F) + K * t * (F * v) ≤ (K + 1) * t * ((v + u) * F) := by
  calc
    _ ≤ (t * (u * F) + K * t * (F * v)) +
        (K * t * (u * F) + t * (F * v)) := le_add_right le_rfl
    _ = _ := by ring

/-- Uniform finite-depth three-index pairing bound. -/
theorem pairing_projection_le {d : ℕ} (m : ℤ) (N : ℕ) (s : ℝ)
    (hs : 0 < s) (hsOne : s ≤ 1) (q r : ℝ≥0∞) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (f g : Vec d → ℝ) (hf : IntegrableOn f (cubeSet (originCube d m)))
    (hg : IntegrableOn g (cubeSet (originCube d m))) :
    ENNReal.ofReal |cubeBesovPairing (originCube d m) f
      (cubeProjection (originCube d m) N g)| ≤
      ENNReal.ofReal (pairingConstant d * s⁻¹) *
        (besovNorm d m s 1 (ENNReal.conjExponent q) (ENNReal.conjExponent r) g *
          negativeBesovNorm d m s r q f) := by
  rw [pairing_projection_telescope _ N f g hf hg]
  have hroot := root_pairing_le m s hs hsOne q r hq hr f g
  have hsum := pairing_increment_sum_le m N s hs hsOne q r hq hr f g hg
  have hc : ENNReal.ofReal (pairingConstant d) =
      (3 : ℝ≥0∞) * (3 ^ d : ℕ) * (3 ^ d : ℕ) + 1 := by
    unfold pairingConstant
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    simp only [ENNReal.ofReal_natCast, ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  calc
    _ ≤ ENNReal.ofReal |cubeAverage (originCube d m) f * cubeAverage (originCube d m) g| +
        ∑ j ∈ Finset.range N, ENNReal.ofReal |cubeAverage (originCube d m)
          (fun x => cubeProjection (originCube d m) (j + 1) f x *
            cubeProjectionResidual (originCube d m) j g x)| := by
      calc
        _ ≤ ENNReal.ofReal (|cubeAverage (originCube d m) f * cubeAverage (originCube d m) g| +
            |∑ j ∈ Finset.range N, cubeAverage (originCube d m)
              (fun x => cubeProjection (originCube d m) (j + 1) f x *
                cubeProjectionResidual (originCube d m) j g x)|) := ENNReal.ofReal_le_ofReal (abs_add_le _ _)
        _ ≤ _ := by
          rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
          gcongr
          exact (ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)).trans_eq
            (ENNReal.ofReal_sum_of_nonneg fun j _ => abs_nonneg _)
    _ ≤ _ := add_le_add hroot hsum
    _ ≤ _ := by
      rw [besovNorm_eq_seminorm_add_root, ENNReal.ofReal_mul (pairingConstant_pos d).le, hc]
      exact absorb_root_and_sum _ _ _ _ _

end SubdiffusiveProcess.Besov
