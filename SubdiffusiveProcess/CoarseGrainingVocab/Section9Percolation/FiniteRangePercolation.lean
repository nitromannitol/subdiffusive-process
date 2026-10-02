import SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation.EventIndependence
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.GoodCube
import Mathlib.Data.Pi.Interval




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

open MeasureTheory ProbabilityTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-! ## The bad-event field of Section 9 good cubes -/



def goodCubeBadEventField (E : GoodCubeEvents Ω d) (n : ℕ) :
    ℕ → Lattice d → Set Ω :=
  fun j z ↦
    let y := (3 : ℝ) ^ n • latticeToVec z
    if j = 0 then (E.localGood n y)ᶜ else E.longBad j n y



def InInfluenceBox (C j : ℕ) (u z : Lattice d) : Prop :=
  latticeDist u z ≤ C * 3 ^ j



def IsPercolationGoodSite (E : ℕ → Lattice d → Set Ω)
    (C : ℕ) (ω : Ω) (z : Lattice d) : Prop :=
  ∀ j u, InInfluenceBox C j u z → ω ∉ E j u



structure GoodCubePercolationLaw (mu : Measure Ω) (E : GoodCubeEvents Ω d)
    (n Cdep : ℕ) : Prop where
  /-- Complete spatial fields are independent as the offset scale varies. -/
  independentScales : IndependentEventScales mu (goodCubeBadEventField E n)
  /-- At offset `j`, subfamilies farther apart than `Cdep * 3^j` are independent. -/
  finiteRange : MultiscaleFiniteRangeIndependentEvents mu
    (fun j ↦ Cdep * 3 ^ j) (goodCubeBadEventField E n)
  /-- The joint indicator-field law is invariant under lattice translations. -/
  translationInvariant : TranslationInvariantEventLaw mu (goodCubeBadEventField E n)

omit mΩ in


theorem isGoodCube_of_isPercolationGoodSite_goodCubeBadEventField
    (E : GoodCubeEvents Ω d) (n C : ℕ) (ω : Ω) (z : Lattice d)
    (hgood : IsPercolationGoodSite (goodCubeBadEventField E n) C ω z) :
    IsGoodCube E ω n ((3 : ℝ) ^ n • latticeToVec z) := by
  constructor
  · by_contra hlocal
    apply hgood 0 z
    · simp only [InInfluenceBox, latticeDist_self, pow_zero]
      omega
    · simpa only [goodCubeBadEventField, if_pos] using hlocal
  · intro j hj hbad
    apply hgood j z
    · simp only [InInfluenceBox, latticeDist_self]
      exact Nat.zero_le _
    · have hj0 : j ≠ 0 := Nat.ne_of_gt hj
      simpa only [goodCubeBadEventField, if_neg hj0] using hbad

/-! ## Finite lattice balls -/



def latticeBallFinset (z : Lattice d) (R : ℕ) : Finset (Lattice d) :=
  Finset.Icc (fun i ↦ z i - R) (fun i ↦ z i + R)



@[simp]
theorem mem_latticeBallFinset_iff {z u : Lattice d} {R : ℕ} :
    u ∈ latticeBallFinset z R ↔ latticeDist z u ≤ R := by
  rw [latticeBallFinset, Finset.mem_Icc, latticeDist_le_iff]
  constructor
  · intro hu i
    rw [← Int.ofNat_le, Int.natCast_natAbs]
    exact Set.mem_Icc_iff_abs_le.mpr ⟨hu.1 i, hu.2 i⟩
  · intro hu
    constructor <;> intro i
    · apply (Set.mem_Icc_iff_abs_le.mp ?_).1
      rw [Int.abs_eq_natAbs, Int.ofNat_le]
      exact hu i
    · apply (Set.mem_Icc_iff_abs_le.mp ?_).2
      rw [Int.abs_eq_natAbs, Int.ofNat_le]
      exact hu i



@[simp]
theorem card_latticeBallFinset (z : Lattice d) (R : ℕ) :
    (latticeBallFinset z R).card = (2 * R + 1) ^ d := by
  classical
  simp only [latticeBallFinset, Pi.card_Icc, Int.card_Icc]
  have hcard (i : Fin d) :
      ((z i + (R : ℤ) + 1 - (z i - (R : ℤ))).toNat) = 2 * R + 1 := by
    rw [show z i + (R : ℤ) + 1 - (z i - (R : ℤ)) = (2 * R + 1 : ℕ) by omega]
    exact Int.toNat_natCast _
  simp_rw [hcard]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ## The influence events from the manuscript -/



def influenceFailure (E : Lattice d → Set Ω) (R : ℕ) (v : Lattice d) : Set Ω :=
  ⋃ u ∈ latticeBallFinset v R, E u



def thickenedInfluenceFailure (E : Lattice d → Set Ω)
    (R J : ℕ) (v : Lattice d) : Set Ω :=
  ⋃ w ∈ latticeBallFinset v J, influenceFailure E R w



theorem measure_influenceFailure_le (E : Lattice d → Set Ω) (R : ℕ)
    (v : Lattice d) (p : ℝ≥0∞) (hprob : ∀ u, μ (E u) ≤ p) :
    μ (influenceFailure E R v) ≤ ((2 * R + 1) ^ d : ℕ) • p := by
  calc
    μ (influenceFailure E R v) ≤ ∑ u ∈ latticeBallFinset v R, μ (E u) :=
      measure_biUnion_finset_le (latticeBallFinset v R) E
    _ ≤ ∑ _u ∈ latticeBallFinset v R, p :=
      Finset.sum_le_sum fun u _hu ↦ hprob u
    _ = ((2 * R + 1) ^ d : ℕ) • p := by
      rw [Finset.sum_const, card_latticeBallFinset]



theorem measure_thickenedInfluenceFailure_le (E : Lattice d → Set Ω)
    (R J : ℕ) (v : Lattice d) (p : ℝ≥0∞) (hprob : ∀ u, μ (E u) ≤ p) :
    μ (thickenedInfluenceFailure E R J v) ≤
      ((2 * J + 1) ^ d : ℕ) • (((2 * R + 1) ^ d : ℕ) • p) := by
  calc
    μ (thickenedInfluenceFailure E R J v) ≤
        ∑ w ∈ latticeBallFinset v J, μ (influenceFailure E R w) :=
      measure_biUnion_finset_le (latticeBallFinset v J) (influenceFailure E R)
    _ ≤ ∑ _w ∈ latticeBallFinset v J, (((2 * R + 1) ^ d : ℕ) • p) :=
      Finset.sum_le_sum fun w _hw ↦ measure_influenceFailure_le E R w p hprob
    _ = ((2 * J + 1) ^ d : ℕ) • (((2 * R + 1) ^ d : ℕ) • p) := by
      rw [Finset.sum_const, card_latticeBallFinset]

/-! ## Finite-range occurrence estimates -/



theorem measure_iInter_event_le_pow_of_finiteRange [IsProbabilityMeasure μ]
    {E : Lattice d → Set Ω} {R : ℕ} {ι : Type*} {z : ι → Lattice d}
    (hindep : FiniteRangeIndependentEvents μ R E)
    (hsep : ∀ i j : ι, i ≠ j → R < latticeDist (z i) (z j))
    (s : Finset ι) (p : ℝ≥0∞) (hprob : ∀ i ∈ s, μ (E (z i)) ≤ p) :
    μ (⋂ i ∈ s, E (z i)) ≤ p ^ s.card := by
  rw [measure_biInter_event_eq_prod_of_finiteRange hindep hsep]
  calc
    ∏ i ∈ s, μ (E (z i)) ≤ ∏ _i ∈ s, p :=
      Finset.prod_le_prod (fun _i _hi ↦ zero_le _) hprob
    _ = p ^ s.card := by rw [Finset.prod_const]



theorem measure_iInter_multiscaleEvent_le_pow_of_finiteRange
    [IsProbabilityMeasure μ] {E : ℕ → Lattice d → Set Ω} {range : ℕ → ℕ}
    (hindep : MultiscaleFiniteRangeIndependentEvents μ range E)
    (j : ℕ) {ι : Type*} {z : ι → Lattice d}
    (hsep : ∀ i k : ι, i ≠ k → range j < latticeDist (z i) (z k))
    (s : Finset ι) (p : ℝ≥0∞) (hprob : ∀ i ∈ s, μ (E j (z i)) ≤ p) :
    μ (⋂ i ∈ s, E j (z i)) ≤ p ^ s.card :=
  measure_iInter_event_le_pow_of_finiteRange (hindep j) hsep s p hprob

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
