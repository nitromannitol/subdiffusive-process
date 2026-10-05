module

public import SubdiffusiveProcess.Sobolev.GridFoldConvolution
public import SubdiffusiveProcess.Analysis.SquareRootConvolution
public import SubdiffusiveProcess.Analysis.TriadicDiscount

@[expose] public section

/-! # Full discounted errors of the actual folded coefficient

The original-grid convolution and one fixed root bound imply both R2
estimates at every observation depth. The two named finite-partition M
inequalities remain explicit on their actual restricted Sobolev responses.
No reflected regularity or new discounted estimate is assumed.
-/
open MeasureTheory Set TopologicalSpace
open scoped NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
variable
  (hD : ∀ J (k : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
    ∀ u : killedSobolevGraph (oddGridCell z r hr (triadicHalf J) k),
      ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) k)).1‖ ≤
      K * ‖subspaceGradient (killedSobolevGraph (oddGridCell z r hr (triadicHalf J) k)) u‖)
  (hN : ∀ J (k : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
    ∀ u : meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf J) k),
      ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) k)).1‖ ≤
      K * ‖subspaceGradient (meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf J) k)) u‖)


/-- One fixed coefficient supplies a single finite bound for every grid defect supremum. -/
theorem triadicDefectSup_bounded (a : PositiveCoefficient (centeredCube z r hr)) (hd : 0 < d) :
    ∃ K : ℝ, ∀ n, triadicDefectSup z hr hD hN a hd n ≤ K := by
  obtain ⟨c, hc, ha⟩ := a.property
  exact ⟨_, triadicDefectSup_le_of_bounds z hr hD hN a hd hc ha
    ((boundedPotential_ae_bound a.val).mono fun x hx => (le_abs_self _).trans hx)⟩

/-- Actual defect sums at every observation depth converge under every strict geometric discount. -/
theorem triadicDefectSup_discount_summable
    (a : PositiveCoefficient (centeredCube z r hr)) (hd : 0 < d) (m : ℕ)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    Summable (fun n => t^n * triadicDefectSup z hr hD hN a hd (m+n)) := by
  obtain ⟨K, hK⟩ := triadicDefectSup_bounded z hr hD hN a hd
  exact geometric_weight_summable (fun n => triadicDefectSup_nonneg z hr hD hN a hd (m+n))
    (fun n => hK (m+n)) ht ht1

/-- The full square-root defect sum is also genuinely summable at each fixed coefficient. -/
theorem triadicDefectSup_sqrt_discount_summable
    (a : PositiveCoefficient (centeredCube z r hr)) (hd : 0 < d) (m : ℕ)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    Summable (fun n => t^n * Real.sqrt (triadicDefectSup z hr hD hN a hd (m+n))) := by
  obtain ⟨K, hK⟩ := triadicDefectSup_bounded z hr hD hN a hd
  exact geometric_weight_summable (fun n => Real.sqrt_nonneg _)
    (fun n => Real.sqrt_le_sqrt (hK (m+n))) ht ht1

/-- Both exact R2 constants for full actual coarse sums, from M finite-partition subadditivity. -/
theorem triadicDefectSup_fold_discounts (hd : 0 < d) (m : ℕ)
    (I P : Finset (Fin d)) (g : C(closedCube z r hr, ℝ)) {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1/2) :
    let a := expPotentialCoefficient (compactPotentialLp (Ω := centeredCube z r hr)
      (closedCube z r hr) g)
    let af := expPotentialCoefficient (compactPotentialLp (Ω := centeredCube z r hr)
      (closedCube z r hr) (g.comp (coordinateFoldOnCube z hr I P)))
    (∀ (N : ℕ) (k : OddGridIndex d (triadicHalf N)) (p : Fin d → ℝ),
      let w := oddGridCenter z r (triadicHalf N) k
      let s := r / (2 * (triadicHalf N : ℝ) + 1)
      let hs : 0 < s := div_pos hr (by positivity)
      let D := observation_killedPoincare z hr hD N k
      let V := observation_meanZeroPoincare z hr hN N k
      let I' := triadicObservationPlanes N I k
      let afU := positiveCoefficientRestrict (oddGridCell_subset z hr (triadicHalf N) k) af
      ∀ J,
        (triadicAdaptiveLabels I' J : Set (TriadicAdaptiveIndex d J)).PairwiseDisjoint
          (fun t => (triadicAdaptiveCell w s hs J t : Set (SpatialCoordinates d))) →
        ((⋃ t ∈ triadicAdaptiveLabels I' J,
          (triadicAdaptiveCell w s hs J t : Set (SpatialCoordinates d)))
          =ᵐ[volume] (centeredCube w s hs : Set (SpatialCoordinates d))) →
        (affineDirichletResponse (centeredCube_isBounded w hs) (hD N k) afU p ≤
          ∑ t ∈ triadicAdaptiveLabels I' J,
            affineDirichletResponse (triadicAdaptiveCell_isBounded w hs J t)
              (triadicAdaptiveCell_killedPoincare w hs D J t)
              (positiveCoefficientRestrict (triadicAdaptiveCell_subset_root w hs J t) afU) p) ∧
        (affineInverseNeumannResponse (hN N k) afU p ≤
          ∑ t ∈ triadicAdaptiveLabels I' J,
            affineInverseNeumannResponse (triadicAdaptiveCell_meanZeroPoincare w hs V J t)
              (positiveCoefficientRestrict (triadicAdaptiveCell_subset_root w hs J t) afU) p)) →
    ((∑' n : ℕ, ((3 : ℝ)^(-s))^n * Real.sqrt (triadicDefectSup z hr hD hN af hd (m+n))) ≤
      (1 + Real.sqrt (3*(d : ℝ))/((3 : ℝ)^(1/2-s)-1)) *
        ∑' n : ℕ, ((3 : ℝ)^(-s))^n * Real.sqrt (triadicDefectSup z hr hD hN a hd (m+n))) ∧
    ((∑' n : ℕ, ((3 : ℝ)^(-(2*s)))^n * triadicDefectSup z hr hD hN af hd (m+n)) ≤
      (1 + 3*(d : ℝ)/((3 : ℝ)^(1-2*s)-1)) *
        ∑' n : ℕ, ((3 : ℝ)^(-(2*s)))^n * triadicDefectSup z hr hD hN a hd (m+n)) := by
  intro a af hSub
  obtain ⟨K, hK⟩ := triadicDefectSup_bounded z hr hD hN a hd
  obtain ⟨L, hL⟩ := triadicDefectSup_bounded z hr hD hN af hd
  let A := fun n => triadicDefectSup z hr hD hN a hd (m+n)
  let B := fun n => triadicDefectSup z hr hD hN af hd (m+n)
  have hA : ∀ n, 0 ≤ A n := fun n => triadicDefectSup_nonneg z hr hD hN a hd (m+n)
  have hB : ∀ n, 0 ≤ B n := fun n => triadicDefectSup_nonneg z hr hD hN af hd (m+n)
  have hKA : ∀ n, A n ≤ K := fun n => hK (m+n)
  have hLB : ∀ n, B n ≤ L := fun n => hL (m+n)
  have hconv : ∀ n, B n ≤ A n + (d : ℝ) * ∑' j, (1/3 : ℝ)^j * A (n+j+1) := by
    intro n
    have h := triadicDefectSup_fold_le_series z hr hD hN hd (m+n) I P g (hSub (m+n))
    convert h using 1
    rw [← tsum_mul_left]
    congr 1
    apply tsum_congr
    intro j
    simp only [A, one_div_pow, Nat.add_assoc]
    ring
  constructor
  · have h := sqrt_convolution_discount_le hA hKA hLB (by positivity : (0 : ℝ) ≤ d)
      (by norm_num : (0 : ℝ) ≤ 1/3) (triadic_sqrt_discount_gap hs1)
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hs)) hconv
    rw [triadic_sqrt_discount_constant (d : ℝ) hs1] at h
    exact h
  · have h := geometric_convolution_discount_le hA hKA hB hLB (by positivity : (0 : ℝ) ≤ d)
      (by norm_num : (0 : ℝ) ≤ 1/3) (triadic_square_discount_gap hs1)
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith : -(2*s) < 0)) hconv
    rw [triadic_square_discount_constant (d : ℝ) hs1] at h
    exact h

end SubdiffusiveProcess
