module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevProjectionBasic
public import Mathlib.Analysis.MeanInequalitiesPow
@[expose] public section

set_option autoImplicit false
open Homogenization MeasureTheory
open scoped ENNReal BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support

noncomputable def weightedProjectionStep {d : ℕ} (Q : TriadicCube d) (j : ℕ) (c : TriadicCube d → ℝ) : Vec d → ℝ := by
  classical
  exact fun x => ∑ R ∈ descendantsAtDepth Q j, if x ∈ cubeSet R then c R else 0

theorem weightedProjection_step_at {d : ℕ} (Q : TriadicCube d) (j : ℕ) (c : TriadicCube d → ℝ) {R : TriadicCube d} (hR : R ∈ descendantsAtDepth Q j) {x : Vec d} (hx : x ∈ cubeSet R) : weightedProjectionStep Q j c x = c R := by
  unfold weightedProjectionStep
  rw [Finset.sum_eq_single_of_mem R hR]
  · simp [hx]
  · intro S hS hSR
    have hdis := pairwiseDisjoint_descendantsAtDepth Q j hR hS (fun h => hSR h.symm)
    have hxS : x ∉ cubeSet S := fun h => hdis.le_bot ⟨hx, h⟩
    simp [hxS]

theorem weightedProjection_step_outside {d : ℕ} (Q : TriadicCube d) (j : ℕ) (c : TriadicCube d → ℝ) {x : Vec d} (hx : x ∉ cubeSet Q) : weightedProjectionStep Q j c x = 0 := by
  unfold weightedProjectionStep
  refine Finset.sum_eq_zero fun R hR => ?_
  have hsub : cubeSet R ⊆ cubeSet Q := cubeSet_subset_of_mem_descendantsAtDepth hR
  have hxR : x ∉ cubeSet R := fun hmem => hx (hsub hmem)
  simp [hxR]

theorem weightedProjection_step_projection {d : ℕ} (Q : TriadicCube d) (j : ℕ) (u : Vec d → ℝ) : weightedProjectionStep Q j (fun R => cubeAverage R u) = cubeProjection Q j u := by
  rfl

theorem weightedProjection_step_memLp {d : ℕ} (ν : Measure (Vec d)) [IsFiniteMeasure ν] (Q : TriadicCube d) (j : ℕ) (c : TriadicCube d → ℝ) (p : ℝ≥0∞) : MemLp (weightedProjectionStep Q j c) p ν := by
  unfold weightedProjectionStep
  apply memLp_finset_sum
  intro R hR
  simpa [Set.indicator] using!
    memLp_indicator_const (μ := ν) (p := p) (s := cubeSet R) (hs := measurableSet_cubeSet R)
      (c := c R) (Or.inr (ne_of_lt (measure_lt_top ν _)))

theorem weightedProjection_step_represent {d : ℕ} (Q : TriadicCube d) (j : ℕ) (c : TriadicCube d → ℝ) (f : Vec d → ℝ) (hcell : ∀ R ∈ descendantsAtDepth Q j, ∀ x ∈ cubeSet R, f x = c R) (hout : ∀ x ∉ cubeSet Q, f x = 0) (hat : ∀ R ∈ descendantsAtDepth Q j, ∀ x ∈ cubeSet R, weightedProjectionStep Q j c x = c R) (hz : ∀ x ∉ cubeSet Q, weightedProjectionStep Q j c x = 0) : f = weightedProjectionStep Q j c := by
  funext x
  by_cases hx : x ∈ cubeSet Q
  · obtain ⟨R, hR, hxR⟩ :=
      exists_mem_descendantsAtDepth_of_mem_cubeSet (Q := Q) (n := j) hx
    rw [hcell R hR x hxR, hat R hR x hxR]
  · rw [hout x hx, hz x hx]

theorem weightedProjection_indicator_integral {d : ℕ} (ν : Measure (Vec d)) (R : TriadicCube d) (a : ℝ≥0∞) : (∫⁻ x, if x ∈ cubeSet R then a else 0 ∂ν) = a * ν (cubeSet R) := by
  simpa [Set.indicator] using! lintegral_indicator_const (μ := ν) (measurableSet_cubeSet R) a

theorem weightedProjection_card_pos {d : ℕ} (Q : TriadicCube d) (j : ℕ) : 0 < ((descendantsAtDepth Q j).card : ℝ) := by
  exact_mod_cast Finset.card_pos.mpr (descendantsAtDepth_nonempty Q j)

theorem weightedProjection_root_l2 {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞) (p : ℝ) (hp : 2 ≤ p) (hsum : (∑ i ∈ s, ((a i) ^ (2 : ℝ)) ^ (p / 2)) ≤ (∑ i ∈ s, (a i) ^ (2 : ℝ)) ^ (p / 2)) : (∑ i ∈ s, (a i) ^ p) ^ (1 / p) ≤ (∑ i ∈ s, (a i) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have hp0 : 0 < p := by linarith
  have hrewrite : ∑ i ∈ s, a i ^ p = ∑ i ∈ s, (a i ^ (2 : ℝ)) ^ (p / 2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← ENNReal.rpow_mul]
    congr 1
    ring
  rw [hrewrite]
  refine (ENNReal.rpow_le_rpow hsum ?_).trans_eq ?_
  · exact div_nonneg zero_le_one (by linarith)
  · rw [← ENNReal.rpow_mul]
    congr 1
    field_simp [ne_of_gt hp0]

theorem weightedProjection_sum_rpow {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞) (p : ℝ) (hp : 1 ≤ p) : (∑ i ∈ s, (a i) ^ p) ≤ (∑ i ∈ s, a i) ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
    simp [ENNReal.zero_rpow_of_pos hp0]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (add_le_add (le_refl ((a i) ^ p)) ih).trans (ENNReal.add_rpow_le_rpow_add _ _ hp)

theorem weightedProjection_weighted_root {ι : Type*} (s : Finset ι) (a w : ι → ℝ≥0∞) (W : ℝ≥0∞) (p : ℝ) (hp : 0 < p) (hw : ∀ i ∈ s, w i ≤ W) : (∑ i ∈ s, a i * w i) ^ (1 / p) ≤ W ^ (1 / p) * (∑ i ∈ s, a i) ^ (1 / p) := by
  have h1 : ∑ i ∈ s, a i * w i ≤ W * ∑ i ∈ s, a i := by
    calc ∑ i ∈ s, a i * w i ≤ ∑ i ∈ s, a i * W :=
          Finset.sum_le_sum fun i _ => mul_le_mul_right (hw i ‹_›) _
      _ = W * ∑ i ∈ s, a i := by rw [← Finset.sum_mul, mul_comm]
  refine (ENNReal.rpow_le_rpow h1 (by positivity)).trans_eq ?_
  exact ENNReal.mul_rpow_of_nonneg W _ (by positivity)

theorem weightedProjection_normalized_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞) (N : ℝ≥0∞) : (∑ i ∈ s, a i * N⁻¹) = (∑ i ∈ s, a i) / N := by
  rw [← Finset.sum_mul, div_eq_mul_inv]

theorem weightedProjection_sum_square_normalize (N S : ℝ≥0∞) (hN0 : N ≠ 0) (hNt : N ≠ ∞) : S ^ (1 / 2 : ℝ) = N ^ (1 / 2 : ℝ) * (S / N) ^ (1 / 2 : ℝ) := by
  calc
    S ^ (1 / 2 : ℝ) = (N * (S / N)) ^ (1 / 2 : ℝ) := by
      rw [ENNReal.mul_div_cancel hN0 hNt]
    _ = N ^ (1 / 2 : ℝ) * (S / N) ^ (1 / 2 : ℝ) :=
      ENNReal.mul_rpow_of_nonneg N (S / N) (by norm_num)

theorem weightedProjection_step_lintegral {d : ℕ} (ν : Measure (Vec d)) (Q : TriadicCube d) (j : ℕ) (c : TriadicCube d → ℝ) (p : ℝ) (_hp : 0 < p) (hpoint : ∀ x, ‖weightedProjectionStep Q j c x‖ₑ ^ p = ∑ R ∈ descendantsAtDepth Q j, (cubeSet R).indicator (fun _ => ‖c R‖ₑ ^ p) x) : (∫⁻ x, ‖weightedProjectionStep Q j c x‖ₑ ^ p ∂ν) = ∑ R ∈ descendantsAtDepth Q j, ‖c R‖ₑ ^ p * ν (cubeSet R) := by
  simp_rw [hpoint]
  rw [lintegral_finset_sum _ (fun R _ => measurable_const.indicator (measurableSet_cubeSet R))]
  apply Finset.sum_congr rfl
  intro R hR
  exact lintegral_indicator_const (measurableSet_cubeSet R) _

theorem weightedProjection_step_lp_formula {d : ℕ} (ν : Measure (Vec d)) (Q : TriadicCube d) (j : ℕ) (c : TriadicCube d → ℝ) (p : ℝ) (hp : 0 < p) (hI : (∫⁻ x, ‖weightedProjectionStep Q j c x‖ₑ ^ p ∂ν) = ∑ R ∈ descendantsAtDepth Q j, ‖c R‖ₑ ^ p * ν (cubeSet R)) : eLpNorm (weightedProjectionStep Q j c) (ENNReal.ofReal p) ν = (∑ R ∈ descendantsAtDepth Q j, ‖c R‖ₑ ^ p * ν (cubeSet R)) ^ (1 / p) := by
  have hm : Measurable (weightedProjectionStep Q j c) := by
    simpa only [weightedProjectionStep, Set.indicator] using!
      (descendantsAtDepth Q j).measurable_sum
        (fun R _ => measurable_const.indicator (measurableSet_cubeSet R))
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := hm.aestronglyMeasurable) (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le, hI]

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
