import SubdiffusiveProcess.Lane4.ProbeAssembly
import SubdiffusiveProcess.Lane4.LogRepresentation
import SubdiffusiveProcess.Sobolev.FoldDiscounts




open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.Lane4

variable {d : ℕ}

/-- The upstream geometric weight is the project's geometric discount times a power. -/
theorem geometricWeight_eq (s : ℝ) (l : ℕ) :
    Homogenization.Book.Ch02.geometricWeight s 2 l =
      Homogenization.Book.Ch02.geometricDiscount s 2 * ((3 : ℝ) ^ (-(2 * s))) ^ l := by
  rw [Homogenization.Book.Ch02.geometricWeight]
  congr 1
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(2 * s))) l, ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

/-- Transfer of a nonnegative, summable real inequality to `ℝ≥0∞`. -/
theorem ennreal_tsum_le_of_real_le {f g : ℕ → ℝ} {C : ℝ}
    (hf0 : ∀ l, 0 ≤ f l) (hg0 : ∀ l, 0 ≤ g l) (hC : 0 ≤ C)
    (hfs : Summable f) (hgs : Summable g)
    (h : ∑' l, f l ≤ C * ∑' l, g l) :
    (∑' l, ENNReal.ofReal (f l)) ≤ ENNReal.ofReal C * ∑' l, ENNReal.ofReal (g l) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg hf0 hfs, ← ENNReal.ofReal_tsum_of_nonneg hg0 hgs,
    ← ENNReal.ofReal_mul hC]
  exact ENNReal.ofReal_le_ofReal h

/-- The folded exponential potential represents the folded field, as an `L^∞` class. -/
theorem expPotentialCoefficient_foldedLogPotential_coeFn
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (I P : Finset (Fin d))
    (b : SpatialCoordinates d → ℝ) (hcont : Continuous b) (hpos : ∀ x, 0 < b x) :
    ((expPotentialCoefficient (Ω := centeredCube z r hr)
          (compactPotentialLp (Ω := centeredCube z r hr) (closedCube z r hr)
            ((logPotentialOnCube z hr b hcont hpos).comp
              (coordinateFoldOnCube z hr I P)))).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        fun x => b (coordinateFold z I P x) := by
  have hsub : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (closedCube z r hr : Set (SpatialCoordinates d)) :=
    centeredCube_subset_closedCube z hr
  filter_upwards [expPotentialCoefficient_coeFn (Ω := centeredCube z r hr)
      (compactPotentialLp (Ω := centeredCube z r hr) (closedCube z r hr)
        ((logPotentialOnCube z hr b hcont hpos).comp (coordinateFoldOnCube z hr I P))),
    compactPotentialLp_on_domain (Ω := centeredCube z r hr) (closedCube z r hr) hsub
      ((logPotentialOnCube z hr b hcont hpos).comp (coordinateFoldOnCube z hr I P)),
    self_mem_ae_restrict (centeredCube z r hr).isOpen.measurableSet] with x h1 h2 hx
  rw [h1, h2 hx]
  exact Real.exp_log (hpos _)

/-- (b) The weighted `ℝ≥0∞` discount, stated purely in terms of two abstract nonnegative
real families.  No probe and no coefficient occurs here, which is what keeps it inside the
elaborator's budget. -/
theorem tsum_geometricWeight_ofReal_le_of_real {F G : ℕ → ℝ} {C : ℝ}
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1 / 2)
    (hF0 : ∀ l, 0 ≤ F l) (hG0 : ∀ l, 0 ≤ G l) (hC : 0 ≤ C)
    (hFs : Summable fun l : ℕ => ((3 : ℝ) ^ (-(2 * s))) ^ l * F l)
    (hGs : Summable fun l : ℕ => ((3 : ℝ) ^ (-(2 * s))) ^ l * G l)
    (h : (∑' l : ℕ, ((3 : ℝ) ^ (-(2 * s))) ^ l * F l) ≤
      C * ∑' l : ℕ, ((3 : ℝ) ^ (-(2 * s))) ^ l * G l) :
    (∑' l : ℕ, ENNReal.ofReal (Homogenization.Book.Ch02.geometricWeight s 2 l) *
        ENNReal.ofReal (F l)) ≤
      ENNReal.ofReal C * ∑' l : ℕ,
        ENNReal.ofReal (Homogenization.Book.Ch02.geometricWeight s 2 l) *
          ENNReal.ofReal (G l) := by
  have hdisc : (0 : ℝ) ≤ Homogenization.Book.Ch02.geometricDiscount s 2 := by
    rw [Homogenization.Book.Ch02.geometricDiscount]
    have : Real.rpow (3 : ℝ) (-s * 2) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by nlinarith)
    linarith
  have ht0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(2 * s)) := Real.rpow_nonneg (by norm_num) _
  have hw0 : ∀ l : ℕ, 0 ≤ Homogenization.Book.Ch02.geometricWeight s 2 l := by
    intro l
    rw [geometricWeight_eq]
    exact mul_nonneg hdisc (pow_nonneg ht0 l)
  simp only [← ENNReal.ofReal_mul (hw0 _)]
  refine ennreal_tsum_le_of_real_le (fun l => mul_nonneg (hw0 l) (hF0 l))
    (fun l => mul_nonneg (hw0 l) (hG0 l)) hC ?_ ?_ ?_
  · simp only [geometricWeight_eq, mul_assoc]
    exact hFs.mul_left _
  · simp only [geometricWeight_eq, mul_assoc]
    exact hGs.mul_left _
  · simp only [geometricWeight_eq, mul_assoc]
    rw [tsum_mul_left, tsum_mul_left]
    calc Homogenization.Book.Ch02.geometricDiscount s 2 *
          ∑' l : ℕ, ((3 : ℝ) ^ (-(2 * s))) ^ l * F l
        ≤ Homogenization.Book.Ch02.geometricDiscount s 2 *
            (C * ∑' l : ℕ, ((3 : ℝ) ^ (-(2 * s))) ^ l * G l) :=
          mul_le_mul_of_nonneg_left h hdisc
      _ = _ := by ring

end SubdiffusiveProcess.Lane4
