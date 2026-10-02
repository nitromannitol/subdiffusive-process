import SubdiffusiveProcess.Paper.thm_c1_response_cell_envelope
import SubdiffusiveProcess.Paper.rem_bank_response_moments
import SubdiffusiveProcess.Sobolev.MeshResponseTest
import SubdiffusiveProcess.Sobolev.BoundaryGrowthEnergy
import SubdiffusiveProcess.Probability.FiniteWeightedMoments

/-! A fixed harmonic mesh converts the cell extension moments into a uniform
reciprocal moment for one nonzero unit-cube source. -/

open MeasureTheory Set TopologicalSpace Homogenization SubdiffusiveProcess
open SubdiffusiveProcess.Lane4 SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal BigOperators ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Paper
noncomputable section

/-- The side of a depth-J odd-grid cell is exactly the triadic scale. -/
theorem aux_thm_c1_response_negative_moment_radius (J : ℕ) :
    1 / (2 * (triadicHalf J : ℝ) + 1) = (3 : ℝ) ^ (-(J : ℤ)) := by
  rw [triadic_denominator, zpow_neg, zpow_natCast, one_div]

/-- The fixed smooth boundary datum contributes a deterministic weight to a cell energy. -/
def aux_thm_c1_response_negative_moment_weight {d : ℕ} (c : ℝ)
    (phi : SpatialCoordinates d → ℝ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) : ℝ :=
  aux_rem_bank_response_moments_Csm d c * r ^ ((d : ℝ) - 2) * r ^ 2 *
    (c2Norm (closedCube w r hr : Set (SpatialCoordinates d)) phi) ^ 2

/-- Each deterministic extension weight is nonnegative. -/
theorem aux_thm_c1_response_negative_moment_weight_nonneg {d : ℕ} (c : ℝ)
    (phi : SpatialCoordinates d → ℝ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    0 ≤ aux_thm_c1_response_negative_moment_weight c phi w r hr := by
  exact mul_nonneg (mul_nonneg (mul_nonneg (aux_rem_bank_response_moments_Csm_nonneg d c)
    (Real.rpow_nonneg hr.le _)) (sq_nonneg _)) (sq_nonneg _)

/-- Smooth cell extension bounds the native cell infimum by its root-chart upper ellipticity. -/
theorem aux_thm_c1_response_negative_moment_cell {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (E : in_J d) (X : in_extension d hd E)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (om : BilateralField d)
    (phi : H1Function (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))
    (hphi : ContDiff ℝ 2 phi.toFun)
    (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hsub : centeredCube w r hr ≤ centeredCube (0 : SpatialCoordinates d) 1 one_pos) :
    cellDirichletInfimum (cutoffCoefficient M H om N)
      (centeredCube w r hr : Set (SpatialCoordinates d))
      (phi.restrict (centeredCube w r hr).isOpen hsub) ≤
      aux_thm_c1_response_negative_moment_weight X.C phi.toFun w r hr *
        E.Lam 0 1 one_pos (cutoffPositiveCoefficient M H om N 0 one_pos) w r (1 / 16) 2 := by
  let v := phi.restrict (centeredCube w r hr).isOpen hsub
  let hP := centeredCube_killedPoincare w hr
  rw [cellDirichletInfimum_eq_dirichletResponse hP
    (cutoffPositiveCoefficient M H om N w hr) _
    (aux_rem_bank_response_moments_lc_cutoff_positive_coe M H om N w hr)]
  have hb := aux_rem_bank_response_moments_cell_smooth hd E X w r hr hr1 hP
    (cutoffPositiveCoefficient M H om N w hr) phi.toFun hphi
    (c2Norm (closedCube w r hr : Set (SpatialCoordinates d)) phi.toFun) le_rfl
    ⟨sobolevDataOfH1 v, sobolevDataOfH1_mem_weak v⟩ (sobolevDataOfH1_fst_coeFn v)
  have heq := aux_thm_c1_response_cell_envelope_Lam_eq E M H N om w r hr hsub
  norm_num only [show ((3 / 4 : ℝ) - 1 / 2) / 4 = 1 / 16 by norm_num] at hb
  rw [heq] at hb
  exact hb.trans_eq (by unfold aux_thm_c1_response_negative_moment_weight; ring)

/-- The mesh energy is bounded by a finite weighted sum of the moment envelopes. -/
theorem aux_thm_c1_response_negative_moment_mesh {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (E : in_J d) (X : in_extension d hd E)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (om : BilateralField d)
    (phi : H1Function (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))
    (hphi : ContDiff ℝ 2 phi.toFun) (J : ℕ) :
    (∑ k : OddGridIndex d (triadicHalf J),
      cellDirichletInfimum (cutoffCoefficient M H om N)
        (oddGridCell (0 : SpatialCoordinates d) 1 one_pos (triadicHalf J) k :
          Set (SpatialCoordinates d))
        (phi.restrict (oddGridCell (0 : SpatialCoordinates d) 1 one_pos
          (triadicHalf J) k).isOpen (oddGridCell_subset 0 one_pos (triadicHalf J) k))) ≤
      ∑ k : OddGridIndex d (triadicHalf J),
        aux_thm_c1_response_negative_moment_weight X.C phi.toFun
          (oddGridCenter 0 1 (triadicHalf J) k) ((3 : ℝ) ^ (-(J : ℤ)))
          (zpow_pos zero_lt_three _) *
        aux_thm_c1_response_cell_envelope_field E M H (oddGridCenter 0 1 (triadicHalf J) k) J N om := by
  apply Finset.sum_le_sum
  intro k _hk
  have hr : 0 < 1 / (2 * (triadicHalf J : ℝ) + 1) := by positivity
  have hr1 : 1 / (2 * (triadicHalf J : ℝ) + 1) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    linarith only [(Nat.cast_nonneg (triadicHalf J) : (0 : ℝ) ≤ (triadicHalf J : ℝ))]
  have h := aux_thm_c1_response_negative_moment_cell hd E X M H N om phi hphi
    (oddGridCenter 0 1 (triadicHalf J) k) _ hr hr1 (oddGridCell_subset 0 one_pos (triadicHalf J) k)
  refine h.trans ?_
  simp only [aux_thm_c1_response_negative_moment_radius]
  apply mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_right (inv_nonneg.mpr (E.lam_pos _ _ _ _ _ _ _ _).le))
    (aux_thm_c1_response_negative_moment_weight_nonneg _ _ _ _ _)

/-- Every continuous positive cutoff coefficient has ordinary ellipticity bounds on the unit cube. -/
theorem aux_thm_c1_response_negative_moment_elliptic {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (om : BilateralField d) :
    ∃ lo hi : ℝ, 0 < lo ∧
      ∀ x ∈ (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
        lo ≤ cutoffCoefficient M H om N x ∧ cutoffCoefficient M H om N x ≤ hi := by
  have hc := cutoffCoefficient_continuous M H om N
  obtain ⟨lo, hlo, hlow⟩ := (closedCube (0 : SpatialCoordinates d) 1 one_pos).isCompact.exists_forall_le'
    hc.continuousOn (fun x _ => cutoffCoefficient_pos M H om N x)
  obtain ⟨hi, hhigh⟩ := (closedCube (0 : SpatialCoordinates d) 1 one_pos).isCompact.bddAbove_image
    hc.continuousOn
  refine ⟨lo, hi, hlo, fun x hx => ?_⟩
  have hx' := centeredCube_subset_closedCube (0 : SpatialCoordinates d) one_pos hx
  exact ⟨hlow x hx', hhigh (mem_image_of_mem _ hx')⟩

/-- The fixed smooth source has positive responses and a model-uniform reciprocal first moment. -/
theorem thm_c1_response_negative_moment {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (X : in_extension d hd E) :
    ∃ delta C : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta →
      ∀ (S : ResponseSpace (centeredCube (0 : SpatialCoordinates d) 1 one_pos)),
      S.space = killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos) →
      ∀ N : ℕ,
        (∀ om, 0 < inverseResponse S (cutoffPositiveCoefficient M H om N 0 one_pos)
          ((sobolevVolumeLoad (testL2 (unitResponseTest d))).comp S.space.subtypeL)) ∧
        MemLp (fun om => (inverseResponse S (cutoffPositiveCoefficient M H om N 0 one_pos)
          ((sobolevVolumeLoad (testL2 (unitResponseTest d))).comp S.space.subtypeL))⁻¹)
          1 (chaosSampleLaw M).toMeasure ∧
        eLpNorm (fun om => (inverseResponse S (cutoffPositiveCoefficient M H om N 0 one_pos)
          ((sobolevVolumeLoad (testL2 (unitResponseTest d))).comp S.space.subtypeL))⁻¹)
          1 (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal C := by
  haveI instDim : NeZero d := ⟨by omega⟩
  obtain ⟨phi, hphi, hdata⟩ := exists_unitResponse_native d
  have hphismooth : ContDiff ℝ ∞ phi.toFun := hphi.symm ▸ (unitResponseTest d).contDiff
  have hphisupport : tsupport phi.toFun ⊆
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) :=
    hphi.symm ▸ (unitResponseTest d).tsupport_subset
  obtain ⟨J, B, hB, htest⟩ := exists_unit_mesh_inverseResponse_bound hd phi hphismooth
    (hphi.symm ▸ (unitResponseTest d).hasCompactSupport) hphisupport
    (by rw [hdata]; exact unitResponseTest_l2_ne_zero d)
  rw [hdata] at htest
  obtain ⟨delta, K, hdelta, hK, hmoment⟩ := thm_c1_response_cell_envelope hd E J
  let weight (k : OddGridIndex d (triadicHalf J)) : ℝ :=
    aux_thm_c1_response_negative_moment_weight X.C phi.toFun
      (oddGridCenter 0 1 (triadicHalf J) k) ((3 : ℝ) ^ (-(J : ℤ))) (zpow_pos zero_lt_three _)
  have hweight : ∀ k, 0 ≤ weight k := fun k =>
    aux_thm_c1_response_negative_moment_weight_nonneg _ _ _ _ _
  have hcell (k : OddGridIndex d (triadicHalf J)) :
      centeredCube (oddGridCenter 0 1 (triadicHalf J) k) ((3 : ℝ) ^ (-(J : ℤ)))
        (zpow_pos zero_lt_three _) ≤ centeredCube (0 : SpatialCoordinates d) 1 one_pos := by
    simpa only [oddGridCell, aux_thm_c1_response_negative_moment_radius] using
      oddGridCell_subset (0 : SpatialCoordinates d) one_pos (triadicHalf J) k
  refine ⟨delta, max 1 (B * ((∑ k, weight k) * K)), hdelta, lt_max_of_lt_left one_pos, ?_⟩
  intro M H hH hMd S hS N
  let F (k : OddGridIndex d (triadicHalf J)) : BilateralField d → ℝ :=
    aux_thm_c1_response_cell_envelope_field E M H (oddGridCenter 0 1 (triadicHalf J) k) J N
  have hFm k : MemLp (F k) 1 (chaosSampleLaw M).toMeasure :=
    (hmoment M H hH hMd _ (hcell k) N).1
  have hFb k : eLpNorm (F k) 1 (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal K :=
    (hmoment M H hH hMd _ (hcell k) N).2
  have hsum := finite_weighted_memLp_bound (chaosSampleLaw M).toMeasure 1 le_rfl
    weight hweight F hK.le hFm hFb
  have hpoint (om : BilateralField d) :
      0 < inverseResponse S (cutoffPositiveCoefficient M H om N 0 one_pos)
          ((sobolevVolumeLoad (testL2 (unitResponseTest d))).comp S.space.subtypeL) ∧
        (inverseResponse S (cutoffPositiveCoefficient M H om N 0 one_pos)
          ((sobolevVolumeLoad (testL2 (unitResponseTest d))).comp S.space.subtypeL))⁻¹ ≤
          B * ∑ k, weight k * F k om := by
    obtain ⟨lo, hi, hlo, hcoeff⟩ := aux_thm_c1_response_negative_moment_elliptic M H N om
    obtain ⟨hpos, hbound⟩ := htest S hS (cutoffPositiveCoefficient M H om N 0 one_pos)
      (cutoffCoefficient M H om N) lo hi hlo (cutoffCoefficient_continuous M H om N) hcoeff
      (aux_rem_bank_response_moments_lc_cutoff_positive_coe M H om N 0 one_pos)
    exact ⟨hpos, hbound.trans (mul_le_mul_of_nonneg_left
      (aux_thm_c1_response_negative_moment_mesh hd E X M H N om phi
        (hphismooth.of_le (WithTop.coe_le_coe.mpr
          (show (2 : ℕ∞) ≤ ⊤ from le_top))) J) hB.le)⟩
  have hRmeas := (aux_rem_bank_response_moments_measurable_inverseResponse M H hH.1 N
    0 one_pos S ((sobolevVolumeLoad (testL2 (unitResponseTest d))).comp S.space.subtypeL)).inv
  have hout := aux_rem_bank_response_moments_memLp_of_envelope (chaosSampleLaw M).toMeasure
    (fun om => (inverseResponse S (cutoffPositiveCoefficient M H om N 0 one_pos)
      ((sobolevVolumeLoad (testL2 (unitResponseTest d))).comp S.space.subtypeL))⁻¹)
    (fun om => ∑ k, weight k * F k om) B ((∑ k, weight k) * K) hB.le 1
    hRmeas.aestronglyMeasurable hsum.1 hsum.2 (Filter.Eventually.of_forall fun om => ?_)
  · exact ⟨fun om => (hpoint om).1, hout.1,
      hout.2.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))⟩
  · refine ⟨(inv_pos.mpr (hpoint om).1).le, ?_, ?_⟩
    · exact Finset.sum_nonneg fun k _ => mul_nonneg (hweight k)
        (aux_thm_c1_response_cell_envelope_nonneg E M H _ J N om)
    · rw [mul_comm]
      exact (hpoint om).2

end
end Paper
