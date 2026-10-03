module

public import SubdiffusiveProcess.Section10.PhysicalLargeMassGrid
public import SubdiffusiveProcess.Section10.PhysicalLargeMassNumeric
public import SubdiffusiveProcess.Section10.PhysicalLargeMassScaling

@[expose] public section

open MeasureTheory SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.Section10

/-- Exactly the mass projection of PhysicalStaticBounds. -/
def PhysicalMassBounds {d : ℕ} (b : SpatialCoordinates d → ℝ) (K : ℝ) : Prop :=
  ∀ x ∈ Metric.ball (0 : SpatialCoordinates d) 2, ∀ r : ℝ, 0 < r → r ≤ 1 →
    weightedMeasure b (Metric.ball x r) ≤ ENNReal.ofReal (K * r ^ ((d : ℝ) - 1 / 2))

theorem PhysicalMassBounds.mono {d : ℕ} {b : SpatialCoordinates d → ℝ}
    {K K' : ℝ} (h : PhysicalMassBounds b K) (hKK' : K ≤ K') : PhysicalMassBounds b K' := by
  intro x hx r hr hr1
  exact (h x hx r hr hr1).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hKK' (Real.rpow_nonneg hr.le _)))

def massSpatialAverage {d : ℕ} (s : ℝ) (K : (Fin d → ℤ) → ℝ) : ℝ :=
  s ^ d * ∑ j ∈ massGlobalGrid d s, K j ^ (2 * d)

def massGlobalConstant {d : ℕ} (s : ℝ) (K : (Fin d → ℤ) → ℝ) : ℝ :=
  ((15 : ℝ) ^ d + 1) * (1 + massSpatialAverage s K)

theorem massGlobalConstant_one {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    {K : (Fin d → ℤ) → ℝ} (hK : ∀ j, 0 ≤ K j) : 1 ≤ massGlobalConstant s K := by
  have hS : 0 ≤ massSpatialAverage s K :=
    mul_nonneg (pow_nonneg hs d) (Finset.sum_nonneg fun j _ => pow_nonneg (hK j) _)
  have hD : 1 ≤ (15 : ℝ) ^ d + 1 := by
    linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 15) d]
  exact one_le_mul_of_one_le_of_one_le hD (by linarith)

/-- The small-radius scaling and the local-center check are deterministic. -/
theorem mass_micro_small {d : ℕ} {s r : ℝ} (hs : 0 < s)
    (b : SpatialCoordinates d → ℝ) (t x : SpatialCoordinates d)
    (hxt : dist x t ≤ s / 3) {K : ℝ}
    (hlocal : PhysicalMassBounds (fun y => b (t + s • y)) K)
    (hr : 0 < r) (hrs : r ≤ s) :
    weightedMeasure b (Metric.ball x r) ≤
      ENNReal.ofReal ((s ^ (1 / 2 : ℝ) * K) * r ^ ((d : ℝ) - 1 / 2)) := by
  have hy : s⁻¹ • (x - t) ∈ Metric.ball (0 : SpatialCoordinates d) 2 := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hs), ← dist_eq_norm]
    have h := mul_le_mul_of_nonneg_left hxt (inv_pos.mpr hs).le
    have heq : s⁻¹ * (s / 3) = (1 / 3 : ℝ) := by field_simp
    rw [heq] at h
    linarith
  rw [mass_affine_ball b hs t x]
  calc
    ENNReal.ofReal (s ^ d) *
        weightedMeasure (fun y => b (t + s • y)) (Metric.ball (s⁻¹ • (x - t)) (r / s))
        ≤ ENNReal.ofReal (s ^ d) * ENNReal.ofReal (K * (r / s) ^ ((d : ℝ) - 1 / 2)) :=
      mul_le_mul_right (hlocal _ hy _ (div_pos hr hs) ((div_le_one hs).mpr hrs)) _
    _ = ENNReal.ofReal ((s ^ (1 / 2 : ℝ) * K) * r ^ ((d : ℝ) - 1 / 2)) := by
      rw [← ENNReal.ofReal_mul (pow_nonneg hs.le d)]
      congr 1
      calc
        s ^ d * (K * (r / s) ^ ((d : ℝ) - 1 / 2)) =
            K * (s ^ d * (r / s) ^ ((d : ℝ) - 1 / 2)) := by ring
        _ = _ := by rw [mass_small_scaling hs hr]; ring

theorem mass_micro_unit {d : ℕ} {s : ℝ} (hs : 0 < s)
    (b : SpatialCoordinates d → ℝ) (t : SpatialCoordinates d) {K : ℝ}
    (hlocal : PhysicalMassBounds (fun y => b (t + s • y)) K) :
    weightedMeasure b (Metric.ball t s) ≤ ENNReal.ofReal (s ^ d * K) := by
  rw [mass_affine_ball b hs t t]
  simpa only [sub_self, smul_zero, div_self hs.ne', Real.one_rpow, mul_one,
    ← ENNReal.ofReal_mul (pow_nonneg hs.le d)] using
    mul_le_mul_right (hlocal 0 (Metric.mem_ball.mpr (by norm_num)) 1 (by norm_num) le_rfl)
      (ENNReal.ofReal (s ^ d))

/-- One finite event controls all balls. No random law or growth promise is
introduced here; the model application supplies every translated local bound. -/
theorem mass_finite_spatial_aggregation {d : ℕ} (hd : 0 < d) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (b : SpatialCoordinates d → ℝ)
    (K : (Fin d → ℤ) → ℝ) (hK : ∀ j, 0 ≤ K j)
    (hloc : ∀ j ∈ massGlobalGrid d s,
      PhysicalMassBounds (fun y => b (massGridCenter (s / 3) j + s • y)) (K j)) :
    PhysicalMassBounds b (massGlobalConstant s K) := by
  classical
  let S := massSpatialAverage s K
  have hS : 0 ≤ S := by
    exact mul_nonneg (pow_nonneg hs.le _) (Finset.sum_nonneg fun j _ => pow_nonneg (hK j) _)
  have hD : 1 ≤ (15 : ℝ) ^ d + 1 := by
    linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 15) d]
  have hglob : 1 + S ≤ massGlobalConstant s K := by
    change 1 + S ≤ ((15 : ℝ) ^ d + 1) * (1 + S)
    nlinarith
  intro x hx r hr hr1
  by_cases hrs : r ≤ s
  · obtain ⟨j, hj, hdist⟩ := massGrid_small_center hs hs1 x hx
    have hpart : s ^ d * K j ^ (2 * d) ≤ S :=
      mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun i _ => pow_nonneg (hK i) _) hj) (pow_nonneg hs.le d)
    have hmaj := (mass_small_majorant hd hs (hK j) hpart).trans hglob
    exact (mass_micro_small hs b _ x hdist (hloc j hj) hr hrs).trans
      (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hmaj (Real.rpow_nonneg hr.le _)))
  · have hsr : s ≤ r := (lt_of_not_ge hrs).le
    let J := massNearGrid s x r
    have hJsub : J ⊆ massGlobalGrid d s := Finset.filter_subset _ _
    have hsum : ∑ j ∈ J, K j ≤ (J.card : ℝ) * r ^ (-1 / 2 : ℝ) +
        r ^ ((d : ℝ) - 1 / 2) * ∑ j ∈ J, K j ^ (2 * d) := by
      calc
        _ ≤ ∑ j ∈ J, (r ^ (-1 / 2 : ℝ) + r ^ ((d : ℝ) - 1 / 2) * K j ^ (2 * d)) :=
          Finset.sum_le_sum fun j _ => mass_scaled_majorant hd hr (hK j)
        _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    have hpowers : s ^ d * ∑ j ∈ J, K j ^ (2 * d) ≤ S := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs.le d)
      exact Finset.sum_le_sum_of_subset_of_nonneg hJsub (fun j _ _ => pow_nonneg (hK j) _)
    have hcard := massNearGrid_weight_card hs hsr x
    have hid : r ^ d * r ^ (-1 / 2 : ℝ) = r ^ ((d : ℝ) - 1 / 2) := by
      rw [← Real.rpow_natCast r d, ← Real.rpow_add hr]
      congr 1
      ring
    have hbound : s ^ d * ∑ j ∈ J, K j ≤
        massGlobalConstant s K * r ^ ((d : ℝ) - 1 / 2) := by
      calc
        _ ≤ s ^ d * ((J.card : ℝ) * r ^ (-1 / 2 : ℝ) +
            r ^ ((d : ℝ) - 1 / 2) * ∑ j ∈ J, K j ^ (2 * d)) :=
          mul_le_mul_of_nonneg_left hsum (pow_nonneg hs.le d)
        _ = (s ^ d * (J.card : ℝ)) * r ^ (-1 / 2 : ℝ) +
            r ^ ((d : ℝ) - 1 / 2) * (s ^ d * ∑ j ∈ J, K j ^ (2 * d)) := by ring
        _ ≤ ((15 : ℝ) ^ d * r ^ d) * r ^ (-1 / 2 : ℝ) +
            r ^ ((d : ℝ) - 1 / 2) * S := by gcongr
        _ = ((15 : ℝ) ^ d + S) * r ^ ((d : ℝ) - 1 / 2) := by rw [mul_assoc, hid]; ring
        _ ≤ massGlobalConstant s K * r ^ ((d : ℝ) - 1 / 2) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr.le _)
          change (15 : ℝ) ^ d + S ≤ ((15 : ℝ) ^ d + 1) * (1 + S)
          nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 15) d]
    calc
      weightedMeasure b (Metric.ball x r)
          ≤ weightedMeasure b (⋃ j ∈ J, Metric.ball (massGridCenter (s / 3) j) s) :=
        measure_mono (massGrid_cover_ball hs hs1 x hx hr1)
      _ ≤ ∑ j ∈ J, weightedMeasure b (Metric.ball (massGridCenter (s / 3) j) s) :=
        measure_biUnion_finset_le _ _
      _ ≤ ∑ j ∈ J, ENNReal.ofReal (s ^ d * K j) :=
        Finset.sum_le_sum fun j hj => mass_micro_unit hs b _ (hloc j (hJsub hj))
      _ = ENNReal.ofReal (s ^ d * ∑ j ∈ J, K j) := by
        rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
        exact fun j _ => mul_nonneg (pow_nonneg hs.le d) (hK j)
      _ ≤ _ := ENNReal.ofReal_le_ofReal hbound

end SubdiffusiveProcess.Section10
