module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.SeminormLimits
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationTestFunctions
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationQuadratic

@[expose] public section

/-! Quadratic drift bounds derived from linear coefficient growth. -/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open Homogenization hiding Vec norm_le_euclideanNorm
open SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
open Filter Topology MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

theorem abs_quadratic_drift_of_linearGrowth {d : ℕ} {c rho : Vec d → ℝ}
    (hc : Differentiable ℝ c) (hcnn : ∀ x, 0 ≤ c x) (hrho : ∀ x, 0 < rho x)
    {K : ℝ} (hK : 0 ≤ K) (hgrowth : ∀ x, euclideanNorm (euclideanGradient c x)+c x ≤ K*rho x*(1+‖x‖))
    (x : Vec d) :
    |coeffFluxDiv c (fun y ↦ 1+euclideanNorm y^2) x/rho x| ≤
      4*((d:ℝ)+1)*K*(1+vecNormSq x) := by
  rw [coeffFluxDiv_one_add_norm_sq hc x, ← euclideanNorm_sq x]
  have hkr : 0 ≤ K*rho x := mul_nonneg hK (hrho x).le
  have h1 : K*rho x*(1+‖x‖) ≤ K*rho x*(1+euclideanNorm x) := by
    gcongr
    exact norm_le_euclideanNorm x
  have hbg : c x + euclideanNorm (euclideanGradient c x) ≤ K*rho x*(1+euclideanNorm x) := by
    linarith [hgrowth x, h1]
  exact abs_quadratic_drift_weighted_scalar (Nat.cast_nonneg d) (euclideanNorm_nonneg x)
    (hcnn x) (euclideanNorm_nonneg (euclideanGradient c x)) hK (hrho x) hbg
    (abs_vecDot_le_euclideanNorm_mul x (euclideanGradient c x))

theorem quadratic_square_translate_le {d : ℕ} (x y : Vec d) :
    (1+vecNormSq y)^2 ≤ 8*((1+vecNormSq x)^2+(vecNormSq (y-x))^2) := by
  -- Step 1
  have htri := euclideanNorm_add_le x (y-x)
  rw [add_sub_cancel] at htri
  -- Step 2
  have h2 := mul_self_le_mul_self (euclideanNorm_nonneg y) htri
  -- Step 3
  have h3 : vecNormSq y ≤ 2*(vecNormSq x + vecNormSq (y-x)) := by
    rw [← euclideanNorm_sq y, ← euclideanNorm_sq x, ← euclideanNorm_sq (y-x)]
    nlinarith [h2, sq_nonneg (euclideanNorm x - euclideanNorm (y-x))]
  -- Step 4
  have qy : 0 ≤ vecNormSq y := vecNormSq_nonneg y
  have qx : 0 ≤ vecNormSq x := vecNormSq_nonneg x
  have qz : 0 ≤ vecNormSq (y-x) := vecNormSq_nonneg (y-x)
  -- Step 5
  have hbound : 1 + vecNormSq y ≤ 2*((1 + vecNormSq x) + vecNormSq (y-x)) := by
    linarith
  have hsq := mul_self_le_mul_self (by linarith) hbound
  nlinarith [hsq, sq_nonneg ((1 + vecNormSq x) - vecNormSq (y-x))]

theorem centered_drift_bounds_of_linearGrowth {d : ℕ} {c rho : Vec d → ℝ}
    (hc : Differentiable ℝ c) (hcnn : ∀ y, 0 ≤ c y) (hrho : ∀ y, 0 < rho y)
    {K : ℝ} (hK : 0 ≤ K)
    (hgrowth : ∀ y, euclideanNorm (euclideanGradient c y)+c y ≤ K*rho y*(1+‖y‖))
    (x y : Vec d) :
    |coeffFluxDiv c (fun z ↦ vecNormSq (z-x)) y/rho y| ≤
      (8*((d:ℝ)+1)*K)*((1+vecNormSq x)+vecNormSq (y-x)) ∧
    c y/rho y ≤ (4*K)*((1+vecNormSq x)+vecNormSq (y-x)) := by
  let r := euclideanNorm x+euclideanNorm (y-x)
  have hr : 0 ≤ r := add_nonneg (euclideanNorm_nonneg x) (euclideanNorm_nonneg (y-x))
  have htri : euclideanNorm y ≤ r := by
    simpa only [add_sub_cancel] using euclideanNorm_add_le x (y-x)
  have hnorm : ‖y‖ ≤ r := (norm_le_euclideanNorm y).trans htri
  have hlin : c y+euclideanNorm (euclideanGradient c y) ≤ K*rho y*(1+r) := by
    have hscaled := mul_le_mul_of_nonneg_left (add_le_add_left hnorm 1)
      (mul_nonneg hK (hrho y).le)
    linarith [hgrowth y, hscaled]
  have hdot : |vecDot (y-x) (euclideanGradient c y)| ≤ r*euclideanNorm (euclideanGradient c y) := by
    refine (abs_vecDot_le_euclideanNorm_mul (y-x) (euclideanGradient c y)).trans ?_
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (euclideanNorm_nonneg x))
      (euclideanNorm_nonneg (euclideanGradient c y))
  have hsquare : 1+r^2 ≤ 2*((1+vecNormSq x)+vecNormSq (y-x)) := by
    simpa only [euclideanNorm_sq, add_assoc] using
      one_add_add_sq_le (euclideanNorm x) (euclideanNorm (y-x))
  constructor
  · rw [coeffFluxDiv_centeredNormSq hc x y]
    have hbase := abs_quadratic_drift_weighted_scalar (Nat.cast_nonneg d) hr
      (hcnn y) (euclideanNorm_nonneg (euclideanGradient c y)) hK (hrho y) hlin hdot
    have hscaled := mul_le_mul_of_nonneg_left hsquare
      (show 0 ≤ 4*((d:ℝ)+1)*K by positivity)
    exact hbase.trans (by nlinarith [hscaled])
  · have hbase := coefficient_ratio_le_quadratic_scalar
      (euclideanNorm_nonneg (euclideanGradient c y)) hK (hrho y) hr le_rfl
      (by simpa only [add_comm (c y)] using hlin)
    have hscaled := mul_le_mul_of_nonneg_left hsquare (show 0 ≤ 2*K by positivity)
    exact hbase.trans (by nlinarith [hscaled])

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
