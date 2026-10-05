module

public import SubdiffusiveProcess.MeyersRegularity.Basic

@[expose] public section

/-! Interior Meyers regularity: BallGeometry. -/

open MeasureTheory Filter Set TopologicalSpace
open Homogenization
open scoped ENNReal NNReal Topology ContDiff BigOperators Pointwise

noncomputable section
namespace SubdiffusiveProcess.MeyersRegularity

open CubeCalderonZygmund

theorem mem_unitBall_iff_norm {d : ℕ} {x : Vec d} {r : ℝ} (hr : 0 < r) :
    x ∈ unitBall d r ↔ ‖HilbertVec.ofVec x‖ < r := by
  change (∑ i : Fin d, (x i - (0 : Vec d) i)^2) < r^2 ↔ _
  simp only [Pi.zero_apply, sub_zero]
  rw [← HilbertVec.norm_sq_eq_sum_sq (HilbertVec.ofVec x)]
  exact sq_lt_sq₀ (norm_nonneg _) hr.le

theorem comparison_parent_subset_ball {d : ℕ} (hd : 2 ≤ d) {r s : ℝ}
    (hr : 1 ≤ r) (hrs : r < s) (hs : s ≤ 3/2) (depth : ℕ)
    {x : Vec d} (hx : x ∈ unitBall d r) {ρ : ℝ} (hρ : 0 < ρ)
    (hρle : ρ ≤ ((s-r)/(d : ℝ)) / (10 * (3 : ℝ)^depth)) :
    axisCube (stoppingComparisonParentCorner x ρ depth)
      (stoppingComparisonParentSide ρ depth) ⊆ unitBall d s := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hden : 0 < 10 * (3 : ℝ)^depth := by positivity
  have hsep : (d : ℝ) * (5 * (3 : ℝ)^depth * ρ) ≤ (s-r)/2 := by
    have h := (le_div_iff₀ hden).mp hρle
    have h' := (le_div_iff₀ hdpos).mp h
    nlinarith
  intro y hy
  rw [stoppingComparisonParent_axisCube_eq_ball x hρ depth] at hy
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have hdist : ‖HilbertVec.ofVec (y-x)‖ < (s-r)/2 := by
    calc
      ‖HilbertVec.ofVec (y-x)‖ ≤ (d : ℝ) * ‖y-x‖ := HilbertVec.norm_ofVec_le_mul_norm _
      _ < (d : ℝ) * (5 * (3 : ℝ)^depth * ρ) := by
        apply mul_lt_mul_of_pos_left _ hdpos
        simpa only [stoppingComparisonParentMultiplier] using hy
      _ ≤ _ := hsep
  have hxn : ‖HilbertVec.ofVec x‖ < r := (mem_unitBall_iff_norm (by linarith : 0 < r)).mp hx
  apply (mem_unitBall_iff_norm (by linarith : 0 < s)).mpr
  have hdecomp : HilbertVec.ofVec y = HilbertVec.ofVec (y-x) + HilbertVec.ofVec x := by
    ext i
    simp
  rw [hdecomp]
  exact (norm_add_le _ _).trans_lt (by linarith)


theorem eBall_eq_translate_smul {d : ℕ} (x0 : Vec d) {R r : ℝ}
    (hR : 0 < R) (hr : 0 < r) :
    Meyers.eBall x0 (r*R) = translateSet x0 (R • unitBall d r) := by
  ext x
  rw [mem_translateSet_iff_sub_mem, Set.mem_smul_set_iff_inv_smul_mem₀ hR.ne']
  have hleft : x ∈ Meyers.eBall x0 (r*R) ↔
      ‖HilbertVec.ofVec (x-x0)‖ < r*R := by
    change (∑ i : Fin d, (x i-x0 i)^2) < (r*R)^2 ↔ _
    have hn : ‖HilbertVec.ofVec (x-x0)‖^2 = ∑ i : Fin d, (x i-x0 i)^2 := by
      simp
    rw [← hn]
    exact sq_lt_sq₀ (norm_nonneg _) (mul_pos hr hR).le
  rw [hleft, mem_unitBall_iff_norm hr]
  have hn : ‖HilbertVec.ofVec (R⁻¹ • (x-x0))‖ = R⁻¹ * ‖HilbertVec.ofVec (x-x0)‖ := by
    rw [← euclideanNorm_eq_norm_ofVec, euclideanNorm_smul, abs_of_pos (inv_pos.mpr hR),
      euclideanNorm_eq_norm_ofVec]
  rw [hn, ← div_eq_inv_mul, div_lt_iff₀ hR]


end SubdiffusiveProcess.MeyersRegularity
