module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevEnergyResidual
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevEnergyStepArithmetic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevProjectionPartition
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevMeasure
@[expose] public section

set_option autoImplicit false
open Homogenization MeasureTheory
open scoped ENNReal BigOperators Topology
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support

theorem weightedProjection_eq_step {d : ℕ} (Q : TriadicCube d) (j : ℕ) (f : Vec d → ℝ) (hcell : ∀ R ∈ descendantsAtDepth Q j, ∃ c : ℝ, ∀ x ∈ cubeSet R, f x = c) (hout : ∀ x ∉ cubeSet Q, f x = 0) : ∃ c : TriadicCube d → ℝ, f = weightedProjectionStep Q j c := by
  classical
  let c : TriadicCube d → ℝ := fun R =>
    if h : R ∈ descendantsAtDepth Q j then Classical.choose (hcell R h) else 0
  refine ⟨c, weightedProjection_step_represent Q j c f ?_ hout ?_ ?_⟩
  · intro R hR x hx
    simpa [c, hR] using Classical.choose_spec (hcell R hR) x hx
  · intro R hR x hx
    exact weightedProjection_step_at Q j c hR hx
  · intro x hx
    exact weightedProjection_step_outside Q j c hx

theorem weightedProjection_card_cast {d : ℕ} (Q : TriadicCube d) (j : ℕ) : ((descendantsAtDepth Q j).card : ℝ≥0∞) = (3 : ℝ≥0∞) ^ ((d : ℝ) * (j : ℝ)) := by
  rw [descendantsAtDepth_card]
  push_cast
  rw [ENNReal.rpow_mul, ENNReal.rpow_natCast, ENNReal.rpow_natCast]

theorem weightedProjection_card_nezero {d : ℕ} (Q : TriadicCube d) (j : ℕ) : ((descendantsAtDepth Q j).card : ℝ≥0∞) ≠ 0 := by
  exact_mod_cast (ne_of_gt (Finset.card_pos.mpr (descendantsAtDepth_nonempty Q j)))

theorem weightedProjection_card_netop {d : ℕ} (Q : TriadicCube d) (j : ℕ) : ((descendantsAtDepth Q j).card : ℝ≥0∞) ≠ ∞ := by
  simp


theorem weightedProjection_lp_one_le (p : ℝ) (hp : 2 ≤ p) : 1 ≤ ENNReal.ofReal p := by
  have h : (1 : ℝ) ≤ p := by linarith
  simpa using ENNReal.ofReal_le_ofReal h

theorem weightedProjection_sum_geometric_enn (A r : ℝ≥0∞) (n : ℕ) : (∑ j ∈ Finset.range n, A * r ^ j) ≤ A * (1 - r)⁻¹ := by
  calc (∑ j ∈ Finset.range n, A * r ^ j)
      ≤ ∑' j : ℕ, A * r ^ j := ENNReal.sum_le_tsum _
    _ = A * (1 - r)⁻¹ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

theorem weightedProjection_convergence_transfer {d : ℕ} (Q : TriadicCube d) (ν : Measure (Vec d)) (hν : ν ≪ normalizedCubeMeasure Q) (u : Vec d → ℝ) (hu : IntegrableOn u (cubeSet Q) volume) : ∀ᵐ x ∂ν, Filter.Tendsto (fun n => cubeProjection Q n u x) Filter.atTop (𝓝 (u x)) := by
  apply hν.ae_le
  change ∀ᵐ x ∂(ENNReal.ofReal (cubeVolume Q)⁻¹ • volume.restrict (cubeSet Q)), _
  exact MeasureTheory.Measure.ae_smul_measure
    (ae_tendsto_cubeProjection_of_integrableOn Q u hu) (ENNReal.ofReal (cubeVolume Q)⁻¹)

theorem weightedProjection_ae_meas_increment {d : ℕ} (Q : TriadicCube d) (ν : Measure (Vec d)) (hν : ν ≪ normalizedCubeMeasure Q) (u : Vec d → ℝ) (j : ℕ) : AEStronglyMeasurable (cubeIncrement Q (j + 1) u) ν := by
  exact AEStronglyMeasurable.mono_ac hν (weightedProjection_increment_memLp Q u j 2).aestronglyMeasurable

theorem weightedProjection_ae_meas_gap {d : ℕ} (Q : TriadicCube d) (ν : Measure (Vec d)) (hν : ν ≪ normalizedCubeMeasure Q) (u : Vec d → ℝ) (n : ℕ) : AEStronglyMeasurable (cubeProjectionGap Q 0 n u) ν := by
  apply AEStronglyMeasurable.mono_ac hν
  unfold cubeProjectionGap
  simp only [Nat.zero_add]
  exact (cubeProjection_memLp Q n 2 u).aestronglyMeasurable.sub
    (cubeProjection_memLp Q 0 2 u).aestronglyMeasurable


theorem weightedProjection_sum_function_apply {d : ℕ} (v : ℕ → Vec d → ℝ) (n : ℕ) : (∑ j ∈ Finset.range n, v j) = fun x => ∑ j ∈ Finset.range n, v j x := by
  funext x
  simp only [Finset.sum_apply]

theorem weightedProjection_geom_power (j : ℕ) : (3 : ℝ≥0∞) ^ (-(j : ℝ) / 4) = ((3 : ℝ≥0∞) ^ (-1 / 4 : ℝ)) ^ j := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  congr 1
  ring

theorem weightedProjection_bound_finite_sum {d : ℕ} (ν : Measure (Vec d)) (v : ℕ → Vec d → ℝ) (p A r : ℝ≥0∞) (hp : 1 ≤ p) (_hm : ∀ j, AEStronglyMeasurable (v j) ν) (hb : ∀ j, eLpNorm (v j) p ν ≤ A * r ^ j) (n : ℕ) : eLpNorm (∑ j ∈ Finset.range n, v j) p ν ≤ A * (1 - r)⁻¹ := by
  calc eLpNorm (∑ j ∈ Finset.range n, v j) p ν
      ≤ ∑ j ∈ Finset.range n, eLpNorm (v j) p ν :=
        eLpNorm_sum_le hp
    _ ≤ ∑ j ∈ Finset.range n, (A * r ^ j) :=
        Finset.sum_le_sum fun j _ => hb j
    _ ≤ A * (1 - r)⁻¹ := weightedProjection_sum_geometric_enn A r n

theorem weightedProjection_proj0_ae {d : ℕ} (Q : TriadicCube d) (ν : Measure (Vec d)) (hν : ν ≪ normalizedCubeMeasure Q) (u : Vec d → ℝ) : cubeProjection Q 0 u =ᵐ[ν] (fun _ => cubeAverage Q u) := by
  exact hν.ae_le (cubeProjection_ae_eq_cubeAverage_of_mem_descendantsAtDepth
    (Q := Q) (R := Q) (j := 0) u (by simp))

theorem weightedProjection_gap_bound {d : ℕ} (Q : TriadicCube d) (ν : Measure (Vec d)) (hν : ν ≪ normalizedCubeMeasure Q) (u : Vec d → ℝ) (p A r : ℝ≥0∞) (hp : 1 ≤ p) (hinc : ∀ j, eLpNorm (cubeIncrement Q (j + 1) u) p ν ≤ A * r ^ j) (n : ℕ) : eLpNorm (cubeProjectionGap Q 0 n u) p ν ≤ A * (1 - r)⁻¹ := by
  have h := weightedProjection_bound_finite_sum ν (fun j => cubeIncrement Q (j + 1) u)
    p A r hp (weightedProjection_ae_meas_increment Q ν hν u) hinc n
  simpa only [weightedProjection_sum_function_apply, weightedProjection_telescope] using h

theorem weightedProjection_gap_tendsto {d : ℕ} (Q : TriadicCube d) (ν : Measure (Vec d)) (hν : ν ≪ normalizedCubeMeasure Q) (u : Vec d → ℝ) (hu : IntegrableOn u (cubeSet Q) volume) : ∀ᵐ x ∂ν, Filter.Tendsto (fun n => cubeProjectionGap Q 0 n u x) Filter.atTop (𝓝 (cubeFluctuation Q u x)) := by
  filter_upwards [weightedProjection_convergence_transfer Q ν hν u hu,
    weightedProjection_proj0_ae Q ν hν u] with x hx hx0
  simpa [cubeProjectionGap, cubeFluctuation, hx0] using hx.sub_const (cubeAverage Q u)

theorem weightedProjection_fluctuation_bound {d : ℕ} (Q : TriadicCube d) (ν : Measure (Vec d)) (hν : ν ≪ normalizedCubeMeasure Q) (u : Vec d → ℝ) (hu : IntegrableOn u (cubeSet Q) volume) (p A r : ℝ≥0∞) (hp : 1 ≤ p) (hinc : ∀ j, eLpNorm (cubeIncrement Q (j + 1) u) p ν ≤ A * r ^ j) : eLpNorm (cubeFluctuation Q u) p ν ≤ A * (1 - r)⁻¹ := by
  exact Lp.eLpNorm_le_of_ae_tendsto
    (Filter.Eventually.of_forall (weightedProjection_gap_bound Q ν hν u p A r hp hinc))
    (weightedProjection_ae_meas_gap Q ν hν u)
    (aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (weightedProjection_ae_meas_gap Q ν hν u)
      (weightedProjection_gap_tendsto Q ν hν u hu))
    (weightedProjection_gap_tendsto Q ν hν u hu)

theorem weightedProjection_geometric_real (A : ℝ) : ENNReal.ofReal A * (1 - (3 : ℝ≥0∞) ^ (-1 / 4 : ℝ))⁻¹ = ENNReal.ofReal (A / (1 - (3 : ℝ) ^ (-1 / 4 : ℝ))) := by
  have hr : 0 < 1 - (3 : ℝ) ^ (-1 / 4 : ℝ) :=
    sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  rw [ENNReal.ofReal_div_of_pos hr,
    ENNReal.ofReal_sub 1 (Real.rpow_nonneg (by norm_num) _),
    ← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 3)]
  norm_num [div_eq_mul_inv]

theorem weightedProjection_constant_pos : 0 < (2 * (3 : ℝ) ^ (1 / 4 : ℝ)) / (1 - (3 : ℝ) ^ (-1 / 4 : ℝ)) := by
  exact div_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _))
    (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)))

theorem weightedProjection_increment_norm_le {d : ℕ} (Q : TriadicCube d) (ν : Measure (Vec d)) (u : Vec d → ℝ) (p : ℝ) (hp : 2 ≤ p) (j : ℕ) (W : ℝ≥0∞) (hν : ∀ R ∈ descendantsAtDepth Q (j + 1), ν (cubeSet R) ≤ W / ((descendantsAtDepth Q (j + 1)).card : ℝ≥0∞)) : eLpNorm (cubeIncrement Q (j + 1) u) (ENNReal.ofReal p) ν ≤ ((W / ((descendantsAtDepth Q (j + 1)).card : ℝ≥0∞)) ^ (1 / p) * ((descendantsAtDepth Q (j + 1)).card : ℝ≥0∞) ^ (1 / 2 : ℝ)) * eLpNorm (cubeIncrement Q (j + 1) u) 2 (normalizedCubeMeasure Q) := by
  obtain ⟨c, hc⟩ := weightedProjection_eq_step Q (j + 1) (cubeIncrement Q (j + 1) u)
    (fun R hR => weightedSobolev_increment_constant_on_descendant j u hR)
    (fun x hx => cubeIncrement_eq_zero_of_not_mem_cubeSet Q (j + 1) u hx)
  rw [hc]
  exact weightedProjection_step_norm_le ν (normalizedCubeMeasure Q) Q (j + 1) c p hp
    ((descendantsAtDepth Q (j + 1)).card : ℝ≥0∞) W
    (weightedProjection_card_nezero Q (j + 1))
    (weightedProjection_card_netop Q (j + 1))
    (fun R hR => weightedSobolev_normalized_cubeSet_descendant hR) hν

/-- The triadic mass bound and the positive half-order Besov bound control the
weighted norm of the ordinary cube fluctuation. -/
theorem weightedProjection_embedding {d : ℕ} (Q : TriadicCube d)
    (ν : Measure (Vec d)) (hν : ν ≪ normalizedCubeMeasure Q)
    (u : Vec d → ℝ) (hu : MemLp u 2 (normalizedCubeMeasure Q))
    (K B p : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B) (hp : 2 ≤ p)
    (hb : -(1 / 2 : ℝ) + (d : ℝ) * (1 / 2 - 1 / p) + 3 / (8 * p) ≤ -(1 / 4 : ℝ))
    (hmass : ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
      ν (cubeSet R) ≤ (ENNReal.ofReal K * (3 : ℝ≥0∞) ^ ((3 / 8 : ℝ) * (j : ℝ))) /
        ((descendantsAtDepth Q j).card : ℝ≥0∞))
    (hdepth : ∀ j : ℕ, cubeBesovDepthSeminorm Q (1 / 2) 2 u j ≤ B) :
    eLpNorm (cubeFluctuation Q u) (ENNReal.ofReal p) ν ≤
      ENNReal.ofReal (((2 * (3 : ℝ) ^ (1 / 4 : ℝ)) / (1 - (3 : ℝ) ^ (-1 / 4 : ℝ))) *
        K ^ (1 / p) * cubeBesovScaleWeight (-1 / 2) Q * B) := by
  have hp0 : 0 < p := by linarith
  let S := cubeBesovScaleWeight (-1 / 2) Q * B
  let A := 2 * (3 : ℝ) ^ (1 / 4 : ℝ) * K ^ (1 / p) * S
  have hS : 0 ≤ S := mul_nonneg (cubeBesovScaleWeight_nonneg _ _) hB
  have hinc : ∀ j : ℕ, eLpNorm (cubeIncrement Q (j + 1) u) (ENNReal.ofReal p) ν ≤
      ENNReal.ofReal A * ((3 : ℝ≥0∞) ^ (-1 / 4 : ℝ)) ^ j := by
    intro j
    have hfirst := weightedProjection_increment_norm_le Q ν u p hp j
      (ENNReal.ofReal K * (3 : ℝ≥0∞) ^ ((3 / 8 : ℝ) * ((j + 1 : ℕ) : ℝ)))
      (hmass (j + 1))
    have hsecond := WeightedEnergy.weightedEnergy_increment_eLpNorm_le Q u B hB hu hdepth j
    refine (hfirst.trans (mul_le_mul_right hsecond _)).trans ?_
    rw [weightedProjection_card_cast]
    have hlast := WeightedEnergy.weightedEnergy_step_ratio_bound
      (D := (d : ℝ)) (p := p) (K := K) (S := S) hp0 hK hS hb j
    simpa only [S, A, Nat.cast_add, Nat.cast_one, mul_assoc,
      weightedProjection_geom_power] using hlast
  have hI : IntegrableOn u (cubeSet Q) volume :=
    integrableOn_of_integrable_normalizedCubeMeasure Q (hu.integrable (by norm_num))
  have hlimit := weightedProjection_fluctuation_bound Q ν hν u hI (ENNReal.ofReal p)
    (ENNReal.ofReal A) ((3 : ℝ≥0∞) ^ (-1 / 4 : ℝ)) (weightedProjection_lp_one_le p hp) hinc
  rw [weightedProjection_geometric_real] at hlimit
  have hcoeff : A / (1 - (3 : ℝ) ^ (-1 / 4 : ℝ)) =
      ((2 * (3 : ℝ) ^ (1 / 4 : ℝ)) / (1 - (3 : ℝ) ^ (-1 / 4 : ℝ))) *
        K ^ (1 / p) * cubeBesovScaleWeight (-1 / 2) Q * B := by
    dsimp [A, S]
    ring
  rw [hcoeff] at hlimit
  exact hlimit

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
