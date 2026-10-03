module

public import SubdiffusiveProcess.Paper.prop_growth_holder_macro_campanato
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

/-! Triadic cell mass bounds imply ball mass bounds for an absolutely continuous finite measure.
This deterministic covering argument has no PDE or probabilistic content. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set Metric SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped BigOperators
noncomputable section
namespace Paper

/-- The neighboring-cell cover bounds the mass of a ball window by the maximal cell mass. -/
theorem aux_lem_as_regularity_cell_measure_cover {d : ℕ} (z : SpatialCoordinates d)
    (mu : Measure (SpatialCoordinates d)) [IsFiniteMeasure mu] (hac : mu ≪ volume)
    (j : ℕ) (k0 : Fin d → ℤ) (x : SpatialCoordinates d) (rad : ℝ) (hrad : 0 < rad)
    (hx : x ∈ ball z (1/2)) (hr : 2*rad ≤ aux_prop_growth_holder_macro_campanato_side j)
    (hk0 : x ∈ closedBall (aux_prop_growth_holder_macro_campanato_center z j k0)
      (aux_prop_growth_holder_macro_campanato_side j/2))
    (T : ℝ) (hT : 0 ≤ T)
    (hcell : ∀ k,aux_prop_growth_holder_macro_campanato_Adm j k →
      mu.real (aux_prop_growth_holder_macro_campanato_cell z j k) ≤ T) :
    mu.real (ball x rad ∩ ball z (1/2)) ≤ (3:ℝ)^d*T := by
  classical
  let F := aux_prop_growth_holder_macro_campanato_family j k0
  have hcov : ∀ᵐ y ∂volume,y ∈ ball x rad ∩ ball z (1/2) →
      y ∈ ⋃ k ∈ F,aux_prop_growth_holder_macro_campanato_cell z j k := by
    filter_upwards [aux_prop_growth_holder_macro_campanato_ae_offgrid z j] with y hoff hy
    obtain ⟨k,hk,-,hyk⟩ := aux_prop_growth_holder_macro_campanato_round z j hy.2
    have hyk' := hyk hoff
    have hkk := aux_prop_growth_holder_macro_campanato_neighbour z (by linarith only [hr]) hk0 hyk' hy.1
    have hkF : k ∈ F := by
      dsimp only [F]
      rw [aux_prop_growth_holder_macro_campanato_family,Finset.mem_filter,Fintype.mem_piFinset]
      refine ⟨fun i => ?_,hk⟩
      have hh := abs_le.mp (hkk i)
      exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
    exact mem_iUnion.mpr ⟨k,mem_iUnion.mpr ⟨hkF,hyk'⟩⟩
  have hmono := ENNReal.toReal_mono (measure_ne_top mu _) (measure_mono_ae (hac.ae_le hcov))
  refine hmono.trans ((measureReal_biUnion_finset_le F _).trans ?_)
  calc _ ≤ ∑ _k ∈ F,T := Finset.sum_le_sum fun k hk => hcell k (Finset.mem_filter.mp hk).2
       _ = (F.card:ℝ)*T := by rw [Finset.sum_const,nsmul_eq_mul]
       _ ≤ (3:ℝ)^d*T := mul_le_mul_of_nonneg_right (aux_prop_growth_holder_macro_campanato_family_card j k0) hT

/-- Uniform triadic cell mass growth gives uniform ball growth. -/
theorem lem_as_regularity_cell_measure {d : ℕ} (z : SpatialCoordinates d)
    (mu : Measure (SpatialCoordinates d)) [IsFiniteMeasure mu] (hac : mu ≪ volume)
    (t K : ℝ) (ht : 0 ≤ t) (hK : 0 ≤ K)
    (hcell : ∀ j : ℕ,∀ k : Fin d → ℤ,aux_prop_growth_holder_macro_campanato_Adm j k →
      mu.real (aux_prop_growth_holder_macro_campanato_cell z j k) ≤
        K*aux_prop_growth_holder_macro_campanato_side j^t) :
    ∀ x ∈ ball z (1/2),∀ rad : ℝ,0 < rad →
      mu.real (ball x rad ∩ ball z (1/2)) ≤ (3:ℝ)^d*(6:ℝ)^t*K*rad^t := by
  intro x hx rad hrad
  have h3 : (1:ℝ) ≤ (3:ℝ)^d := one_le_pow₀ (by norm_num)
  by_cases hsmall : 2*rad ≤ 1
  · obtain ⟨j,hj1,hj2⟩ := exists_nat_pow_near (x := (2*rad)⁻¹)
      (by rw [le_inv_comm₀ (by norm_num) (by positivity)]; simpa only [one_mul,div_one,inv_one] using hsmall)
      (by norm_num : (1:ℝ)<3)
    have hsj : 2*rad ≤ aux_prop_growth_holder_macro_campanato_side j := by
      unfold aux_prop_growth_holder_macro_campanato_side
      rw [le_inv_comm₀ (by positivity) (by positivity)]
      exact hj1
    have hsnext : aux_prop_growth_holder_macro_campanato_side (j+1) < 2*rad := by
      unfold aux_prop_growth_holder_macro_campanato_side
      rw [inv_lt_comm₀ (by positivity) (by positivity)]
      exact hj2
    have hs6 : aux_prop_growth_holder_macro_campanato_side j ≤ 6*rad := by
      rw [aux_prop_growth_holder_macro_campanato_side_succ j]
      linarith only [hsnext]
    obtain ⟨k0,-,hk0,-⟩ := aux_prop_growth_holder_macro_campanato_round z j hx
    have hh := aux_lem_as_regularity_cell_measure_cover z mu hac j k0 x rad hrad hx hsj hk0
      (K*aux_prop_growth_holder_macro_campanato_side j^t)
      (mul_nonneg hK (Real.rpow_nonneg (aux_prop_growth_holder_macro_campanato_side_pos j).le _)) (hcell j)
    have hp := Real.rpow_le_rpow (aux_prop_growth_holder_macro_campanato_side_pos j).le hs6 ht
    rw [Real.mul_rpow (by norm_num) hrad.le] at hp
    have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ (3:ℝ)^d*K by positivity)
    nlinarith only [hh,hm]
  · have hroot := hcell 0 (fun _ => 0) (fun i => by norm_num)
    have heq : aux_prop_growth_holder_macro_campanato_cell z 0 (fun _ => 0) = ball z (1/2) := by
      have hc : aux_prop_growth_holder_macro_campanato_center z 0 (fun _ => 0) = z := by
        funext i
        change z i+((3:ℝ)^0)⁻¹*((0:ℤ):ℝ)=z i
        rw [Int.cast_zero,mul_zero,add_zero]
      change ball (aux_prop_growth_holder_macro_campanato_center z 0 (fun _ => 0)) (((3:ℝ)^0)⁻¹/2) = _
      rw [hc,pow_zero,inv_one]
    rw [heq,aux_prop_growth_holder_macro_campanato_side,pow_zero,inv_one,Real.one_rpow,mul_one] at hroot
    have hp : 1 ≤ (6:ℝ)^t*rad^t := by
      rw [← Real.mul_rpow (by norm_num) hrad.le]
      apply Real.one_le_rpow _ ht
      linarith only [le_of_not_ge hsmall]
    have hm := mul_le_mul h3 hp zero_le_one (by positivity : 0 ≤ (3:ℝ)^d)
    have hk := mul_le_mul_of_nonneg_right hm hK
    have hh : mu.real (ball x rad ∩ ball z (1/2)) ≤ K := (measureReal_mono inter_subset_right).trans hroot
    nlinarith only [hh,hk]

end Paper
