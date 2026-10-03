module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowLocalPerCell
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

variable {X ι : Type*} [MeasurableSpace X]

/-- The positive test energy on one cell: a within-cell fractional term plus
a massive `L²` term.  The kernel and density are kept abstract and
nonnegative; the resolvent application inserts the Gagliardo kernel and the
squared norm of the test field. -/
def fluxRowLocalPositiveEnergy (mu : Measure X) (U : Set X)
    (massWeight : ℝ≥0∞) (kernel : X × X → ℝ≥0∞)
    (density : X → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ z in U ×ˢ U, kernel z ∂(mu.prod mu)) +
    massWeight * ∫⁻ x in U, density x ∂mu

/-- The corresponding whole-space positive energy. -/
def fluxRowGlobalPositiveEnergy (mu : Measure X) (globalMassWeight : ℝ≥0∞)
    (kernel : X × X → ℝ≥0∞) (density : X → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ z, kernel z ∂(mu.prod mu)) +
    globalMassWeight * ∫⁻ x, density x ∂mu



theorem sum_fluxRowLocalPositiveEnergy_le_global
    (mu : Measure X) (cells : Finset ι) (U : ι → Set X)
    (hmeas : ∀ i ∈ cells, MeasurableSet (U i))
    (hdisj : (cells : Set ι).PairwiseDisjoint U)
    (massWeight : ι → ℝ≥0∞) (globalMassWeight : ℝ≥0∞)
    (hweight : ∀ i ∈ cells, massWeight i ≤ globalMassWeight)
    (kernel : X × X → ℝ≥0∞) (density : X → ℝ≥0∞) :
    (∑ i ∈ cells,
      fluxRowLocalPositiveEnergy mu (U i) (massWeight i) kernel density) ≤
      fluxRowGlobalPositiveEnergy mu globalMassWeight kernel density := by
  classical
  have hprodMeas : ∀ i ∈ cells, MeasurableSet (U i ×ˢ U i) :=
    fun i hi ↦ (hmeas i hi).prod (hmeas i hi)
  have hprodDisj : (cells : Set ι).PairwiseDisjoint (fun i ↦ U i ×ˢ U i) := by
    intro i hi j hj hij
    exact Set.disjoint_prod.mpr (Or.inl (hdisj hi hj hij))
  have hfrac :
      (∑ i ∈ cells,
        ∫⁻ z in U i ×ˢ U i, kernel z ∂(mu.prod mu)) ≤
        ∫⁻ z, kernel z ∂(mu.prod mu) := by
    rw [← lintegral_biUnion_finset hprodDisj hprodMeas]
    simpa only [Measure.restrict_univ] using
      (lintegral_mono_set (μ := mu.prod mu) (f := kernel)
        (show (⋃ i ∈ cells, U i ×ˢ U i) ⊆ Set.univ from subset_univ _))
  have hmassSets :
      (∑ i ∈ cells, ∫⁻ x in U i, density x ∂mu) ≤
        ∫⁻ x, density x ∂mu := by
    rw [← lintegral_biUnion_finset hdisj hmeas]
    simpa only [Measure.restrict_univ] using
      (lintegral_mono_set (μ := mu) (f := density)
        (show (⋃ i ∈ cells, U i) ⊆ Set.univ from subset_univ _))
  have hmass :
      (∑ i ∈ cells, massWeight i * ∫⁻ x in U i, density x ∂mu) ≤
        globalMassWeight * ∫⁻ x, density x ∂mu := by
    calc
      (∑ i ∈ cells, massWeight i * ∫⁻ x in U i, density x ∂mu) ≤
          ∑ i ∈ cells,
            globalMassWeight * ∫⁻ x in U i, density x ∂mu := by
        gcongr with i hi
        exact hweight i hi
      _ = globalMassWeight *
          (∑ i ∈ cells, ∫⁻ x in U i, density x ∂mu) := by
        rw [Finset.mul_sum]
      _ ≤ globalMassWeight * ∫⁻ x, density x ∂mu :=
        mul_le_mul_right hmassSets globalMassWeight
  rw [fluxRowGlobalPositiveEnergy]
  simp_rw [fluxRowLocalPositiveEnergy]
  rw [Finset.sum_add_distrib]
  exact add_le_add hfrac hmass

/-- The sum of the volume-weighted squared local negative norms. -/
def fluxRowLocalNegativeSumSq (cells : Finset ι)
    (volume localNegative : ι → ℝ) : ℝ :=
  ∑ i ∈ cells, volume i * localNegative i ^ 2

/-- The analogous volume-weighted positive test cost. -/
def fluxRowLocalTestSumSq (cells : Finset ι)
    (volume localTest : ι → ℝ) : ℝ :=
  ∑ i ∈ cells, volume i * localTest i ^ 2

/-- The physical pairing reconstructed from normalized cell pairings. -/
def fluxRowLocalizedPairing (cells : Finset ι)
    (volume pairing : ι → ℝ) : ℝ :=
  ∑ i ∈ cells, volume i * pairing i

/-- Weighted Cauchy--Schwarz for normalized cell pairings.  The factor
`volume i` converts the normalized local duality pairing back to the physical
integral on the cell. -/
theorem fluxRowLocalizedPairing_sq_le
    (cells : Finset ι) (volume localNegative localTest pairing : ι → ℝ)
    (hvolume : ∀ i ∈ cells, 0 ≤ volume i)
    (hnegative : ∀ i ∈ cells, 0 ≤ localNegative i)
    (htest : ∀ i ∈ cells, 0 ≤ localTest i)
    (hpair : ∀ i ∈ cells,
      |pairing i| ≤ localNegative i * localTest i) :
    fluxRowLocalizedPairing cells volume pairing ^ 2 ≤
      fluxRowLocalNegativeSumSq cells volume localNegative *
        fluxRowLocalTestSumSq cells volume localTest := by
  have habs : |fluxRowLocalizedPairing cells volume pairing| ≤
      ∑ i ∈ cells, volume i * localNegative i * localTest i := by
    calc
      |fluxRowLocalizedPairing cells volume pairing| =
          |∑ i ∈ cells, volume i * pairing i| := rfl
      _ ≤ ∑ i ∈ cells, |volume i * pairing i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ cells, volume i * |pairing i| := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul, abs_of_nonneg (hvolume i hi)]
      _ ≤ ∑ i ∈ cells, volume i *
          (localNegative i * localTest i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hpair i hi) (hvolume i hi)
      _ = ∑ i ∈ cells, volume i * localNegative i * localTest i := by
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hsumNonneg :
      0 ≤ ∑ i ∈ cells, volume i * localNegative i * localTest i := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg
      (mul_nonneg (hvolume i hi) (hnegative i hi)) (htest i hi)
  calc
    fluxRowLocalizedPairing cells volume pairing ^ 2 =
        |fluxRowLocalizedPairing cells volume pairing| ^ 2 := by
      rw [sq_abs]
    _ ≤ (∑ i ∈ cells,
        volume i * localNegative i * localTest i) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) hsumNonneg).2 habs
    _ ≤ (∑ i ∈ cells, volume i * localNegative i ^ 2) *
          ∑ i ∈ cells, volume i * localTest i ^ 2 := by
      let r : ι → ℝ := fun i ↦ volume i * localNegative i * localTest i
      let f : ι → ℝ := fun i ↦ volume i * localNegative i ^ 2
      let g : ι → ℝ := fun i ↦ volume i * localTest i ^ 2
      have hf : ∀ i ∈ cells, 0 ≤ f i := by
        intro i hi
        exact mul_nonneg (hvolume i hi) (sq_nonneg _)
      have hg : ∀ i ∈ cells, 0 ≤ g i := by
        intro i hi
        exact mul_nonneg (hvolume i hi) (sq_nonneg _)
      have hr : ∀ i ∈ cells, r i ^ 2 = f i * g i := by
        intro i _
        dsimp [r, f, g]
        ring
      simpa only [r, f, g] using
        Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul cells hf hg hr
    _ = fluxRowLocalNegativeSumSq cells volume localNegative *
        fluxRowLocalTestSumSq cells volume localTest := rfl



theorem fluxRowDeterministicLocalization
    (cells : Finset ι) (volume localNegative localTest pairing : ι → ℝ)
    (globalTest C : ℝ)
    (hvolume : ∀ i ∈ cells, 0 ≤ volume i)
    (hnegative : ∀ i ∈ cells, 0 ≤ localNegative i)
    (htest : ∀ i ∈ cells, 0 ≤ localTest i)
    (hpair : ∀ i ∈ cells,
      |pairing i| ≤ localNegative i * localTest i)
    (hpositive : fluxRowLocalTestSumSq cells volume localTest ≤
      C * globalTest ^ 2) :
    fluxRowLocalizedPairing cells volume pairing ^ 2 ≤
      C * fluxRowLocalNegativeSumSq cells volume localNegative *
        globalTest ^ 2 := by
  have hlocalNonneg :
      0 ≤ fluxRowLocalNegativeSumSq cells volume localNegative := by
    unfold fluxRowLocalNegativeSumSq
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hvolume i hi) (sq_nonneg _)
  calc
    fluxRowLocalizedPairing cells volume pairing ^ 2 ≤
        fluxRowLocalNegativeSumSq cells volume localNegative *
          fluxRowLocalTestSumSq cells volume localTest :=
      fluxRowLocalizedPairing_sq_le cells volume localNegative localTest pairing
        hvolume hnegative htest hpair
    _ ≤ fluxRowLocalNegativeSumSq cells volume localNegative *
          (C * globalTest ^ 2) := by
      exact mul_le_mul_of_nonneg_left hpositive hlocalNonneg
    _ = C * fluxRowLocalNegativeSumSq cells volume localNegative *
        globalTest ^ 2 := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
