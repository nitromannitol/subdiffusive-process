import SubdiffusiveProcess.Sobolev.HolderTraceScaling

/-! A normalized Hölder bound controls the weaker seminorm on the physical cube boundary.
This file establishes the quantitative seminorm transfer only; it does not construct a trace
extension or a Sobolev form-domain representative.
-/

open Set MeasureTheory
open SubdiffusiveProcess.Lane4
open scoped Topology BigOperators

noncomputable section
namespace SubdiffusiveProcess

private def normalizedBoundaryPoint {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (x : SpatialCoordinates d) : SpatialCoordinates d := r⁻¹ • (x - z)

private def normalizedBoundarySet {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) :
    Set (SpatialCoordinates d) :=
  normalizedBoundaryPoint z r '' frontier (Metric.ball z (r / 2))

private theorem normalizedBoundaryPoint_mem_closedCube {d : ℕ}
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) {x : SpatialCoordinates d}
    (hx : x ∈ frontier (Metric.ball z (r / 2))) :
    normalizedBoundaryPoint z r x ∈
      (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
  have hxs : dist x z = r / 2 := Metric.frontier_ball_subset_sphere hx
  have hnorm : dist (normalizedBoundaryPoint z r x) 0 = 1 / 2 := by
    calc
      dist (normalizedBoundaryPoint z r x) 0 =
          ‖normalizedBoundaryPoint z r x‖ := by
            simpa only [sub_zero] using (dist_eq_norm
              (normalizedBoundaryPoint z r x) (0 : SpatialCoordinates d))
      _ = ‖r⁻¹‖ * ‖x - z‖ := norm_smul _ _
      _ = r⁻¹ * dist x z := by
        rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hr.le), ← dist_eq_norm]
      _ = 1 / 2 := by
        rw [hxs]
        calc
          r⁻¹ * (r / 2) = (r⁻¹ * r) / 2 := by rw [← mul_div_assoc]
          _ = 1 / 2 := by rw [inv_mul_cancel₀ hr.ne']
  change dist (normalizedBoundaryPoint z r x) 0 ≤ 1 / 2
  rw [hnorm]

private theorem normalizedBoundaryPoint_reconstruct {d : ℕ}
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (x : SpatialCoordinates d) :
    z + r • normalizedBoundaryPoint z r x = x := by
  simp only [normalizedBoundaryPoint, smul_smul, mul_inv_cancel₀ hr.ne', one_smul,
    add_sub_cancel]

private theorem normalizedBoundaryPoint_injective {d : ℕ}
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) {x y : SpatialCoordinates d}
    (hxy : normalizedBoundaryPoint z r x = normalizedBoundaryPoint z r y) : x = y := by
  calc
    x = z + r • normalizedBoundaryPoint z r x :=
      (normalizedBoundaryPoint_reconstruct z hr x).symm
    _ = z + r • normalizedBoundaryPoint z r y := by rw [hxy]
    _ = y := normalizedBoundaryPoint_reconstruct z hr y

private theorem normalizedBoundaryPoint_euclideanDistance {d : ℕ}
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (x y : SpatialCoordinates d) :
    Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) =
      r * Real.sqrt (∑ j : Fin d,
        (normalizedBoundaryPoint z r x j - normalizedBoundaryPoint z r y j) ^ 2) := by
  have hcoord : ∀ j : Fin d, x j - y j =
      r * (normalizedBoundaryPoint z r x j - normalizedBoundaryPoint z r y j) := by
    intro j
    have hxj : x j = z j + r * normalizedBoundaryPoint z r x j := by
      have h := congrArg (fun w : SpatialCoordinates d => w j)
        (normalizedBoundaryPoint_reconstruct z hr x).symm
      simpa only [Pi.add_apply, Pi.smul_apply] using h
    have hyj : y j = z j + r * normalizedBoundaryPoint z r y j := by
      have h := congrArg (fun w : SpatialCoordinates d => w j)
        (normalizedBoundaryPoint_reconstruct z hr y).symm
      simpa only [Pi.add_apply, Pi.smul_apply] using h
    linarith only [hxj, hyj]
  have hsum : (∑ j : Fin d, (x j - y j) ^ 2) =
      r ^ 2 * (∑ j : Fin d,
        (normalizedBoundaryPoint z r x j - normalizedBoundaryPoint z r y j) ^ 2) := by
    calc
      _ = ∑ j : Fin d,
          (r * (normalizedBoundaryPoint z r x j - normalizedBoundaryPoint z r y j)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hcoord j]
      _ = ∑ j : Fin d, r ^ 2 *
          (normalizedBoundaryPoint z r x j - normalizedBoundaryPoint z r y j) ^ 2 := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [mul_pow]
      _ = r ^ 2 * (∑ j : Fin d,
          (normalizedBoundaryPoint z r x j - normalizedBoundaryPoint z r y j) ^ 2) := by
            rw [Finset.mul_sum]
  calc
    Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) =
        Real.sqrt (r ^ 2 * (∑ j : Fin d,
          (normalizedBoundaryPoint z r x j - normalizedBoundaryPoint z r y j) ^ 2)) := by
            rw [hsum]
    _ = Real.sqrt (r ^ 2) * Real.sqrt (∑ j : Fin d,
          (normalizedBoundaryPoint z r x j - normalizedBoundaryPoint z r y j) ^ 2) :=
            Real.sqrt_mul (sq_nonneg r) _
    _ = r * Real.sqrt (∑ j : Fin d,
          (normalizedBoundaryPoint z r x j - normalizedBoundaryPoint z r y j) ^ 2) := by
            rw [Real.sqrt_sq_eq_abs, abs_of_pos hr]

private theorem normalizedBoundarySet_subset_unitCube {d : ℕ}
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    normalizedBoundarySet z r ⊆
      (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
  rintro u ⟨x, hx, rfl⟩
  exact normalizedBoundaryPoint_mem_closedCube z hr hx

private theorem normalizedBoundarySet_euclideanDiameter_le {d : ℕ}
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) {u v : SpatialCoordinates d}
    (hu : u ∈ normalizedBoundarySet z r) (hv : v ∈ normalizedBoundarySet z r) :
    Real.sqrt (∑ j : Fin d, (u j - v j) ^ 2) ≤ Real.sqrt d := by
  have huCube := normalizedBoundarySet_subset_unitCube z hr hu
  have hvCube := normalizedBoundarySet_subset_unitCube z hr hv
  change dist u 0 ≤ 1 / 2 at huCube
  change dist v 0 ≤ 1 / 2 at hvCube
  have huNorm : ‖u‖ ≤ 1 / 2 := by
    simpa only [dist_eq_norm, sub_zero] using huCube
  have hvNorm : ‖v‖ ≤ 1 / 2 := by
    simpa only [dist_eq_norm, sub_zero] using hvCube
  have hcoord : ∀ j : Fin d, (u j - v j) ^ 2 ≤ 1 := by
    intro j
    have huj : |u j| ≤ 1 / 2 := by
      calc
        |u j| = ‖u j‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖u‖ := norm_le_pi_norm u j
        _ ≤ 1 / 2 := huNorm
    have hvj : |v j| ≤ 1 / 2 := by
      calc
        |v j| = ‖v j‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖v‖ := norm_le_pi_norm v j
        _ ≤ 1 / 2 := hvNorm
    have habs : |u j - v j| ≤ 1 := by
      calc
        |u j - v j| ≤ |u j| + |v j| := abs_sub _ _
        _ ≤ 1 / 2 + 1 / 2 := add_le_add huj hvj
        _ = 1 := by linarith only []
    have hsquare : |u j - v j| ^ 2 ≤ 1 ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (zero_le_one : (0 : ℝ) ≤ 1)).mpr habs
    simpa only [sq_abs, one_pow] using hsquare
  have hsum : (∑ j : Fin d, (u j - v j) ^ 2) ≤ (d : ℝ) := by
    calc
      _ ≤ ∑ j : Fin d, (1 : ℝ) :=
        Finset.sum_le_sum (fun j hj => hcoord j)
      _ = (d : ℝ) := by simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]
  exact Real.sqrt_le_sqrt hsum

/-- A normalized cube Hölder norm bounds the weaker physical boundary seminorm with its exact scale factor. -/
theorem scaled_boundary_holderSeminorm_le_normalized_norm
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (alpha beta c B : ℝ) (hba : beta ≤ alpha) (hb : 0 < beta) (hB : 0 ≤ B)
    (U : SpatialCoordinates d → ℝ)
    (hU : IsHolderOn alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
      (fun x => U (z + r • x) - c))
    (hNorm : cAlphaNorm alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
      (fun x => U (z + r • x) - c) ≤ B) :
    IsHolderOn beta (frontier (Metric.ball z (r / 2))) U ∧
      r ^ beta * holderSeminorm beta (frontier (Metric.ball z (r / 2))) U ≤
        (Real.sqrt d) ^ (alpha - beta) * B := by
  let Q : Set (SpatialCoordinates d) :=
    closedCube (0 : SpatialCoordinates d) 1 one_pos
  let T : Set (SpatialCoordinates d) := normalizedBoundarySet z r
  let V : SpatialCoordinates d → ℝ := fun x => U (z + r • x) - c
  have hsub : T ⊆ Q := by
    exact normalizedBoundarySet_subset_unitCube z hr
  have hdiam : ∀ x ∈ T, ∀ y ∈ T,
      Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt d := by
    intro x hx y hy
    exact normalizedBoundarySet_euclideanDiameter_le z hr hx hy
  have hV : IsHolderOn alpha Q V := hU
  obtain ⟨hVbeta, hVbetaBound⟩ :=
    holderSeminorm_le_of_diameter hsub hba (Real.sqrt_nonneg _) hV hdiam
  have hAbsNonneg : 0 ≤ sSup {w : ℝ | ∃ x ∈ Q, w = |V x|} := by
    apply Real.sSup_nonneg
    rintro w ⟨x, hx, rfl⟩
    exact abs_nonneg _
  have hAlphaBound : holderSeminorm alpha Q V ≤ B := by
    have hAlphaNorm : holderSeminorm alpha Q V ≤ cAlphaNorm alpha Q V := by
      unfold Lane4.cAlphaNorm
      exact le_add_of_nonneg_left hAbsNonneg
    exact hAlphaNorm.trans hNorm
  let C : ℝ := (Real.sqrt d) ^ (alpha - beta) * B
  have hCnonneg : 0 ≤ C := by
    exact mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) hB
  have hVbetaBoundC : holderSeminorm beta T V ≤ C := by
    calc
      holderSeminorm beta T V ≤ holderSeminorm alpha Q V * (Real.sqrt d) ^ (alpha - beta) :=
        hVbetaBound
      _ ≤ B * (Real.sqrt d) ^ (alpha - beta) :=
        mul_le_mul_of_nonneg_right hAlphaBound (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
      _ = C := by rw [mul_comm]
  have hpowPos : 0 < r ^ beta := Real.rpow_pos_of_pos hr beta
  have hratio : ∀ q ∈ holderRatioSet beta (frontier (Metric.ball z (r / 2))) U,
      q ≤ C / r ^ beta := by
    rintro q ⟨x, hx, y, hy, hxy, rfl⟩
    let x' := normalizedBoundaryPoint z r x
    let y' := normalizedBoundaryPoint z r y
    have hx' : x' ∈ T := ⟨x, hx, rfl⟩
    have hy' : y' ∈ T := ⟨y, hy, rfl⟩
    have hxy' : x' ≠ y' := by
      intro heq
      exact hxy (normalizedBoundaryPoint_injective z hr heq)
    have he' : 0 < Real.sqrt (∑ j : Fin d, (x' j - y' j) ^ 2) :=
      sqrt_sum_sq_sub_pos hxy'
    have hquot : |V x' - V y'| /
        (Real.sqrt (∑ j : Fin d, (x' j - y' j) ^ 2)) ^ beta ≤
          holderSeminorm beta T V :=
      le_csSup hVbeta ⟨x', hx', y', hy', hxy', rfl⟩
    have hquotNum : |V x' - V y'| ≤ holderSeminorm beta T V *
        (Real.sqrt (∑ j : Fin d, (x' j - y' j) ^ 2)) ^ beta :=
      (div_le_iff₀ (Real.rpow_pos_of_pos he' beta)).mp hquot
    have hquotNumC : |V x' - V y'| ≤ C *
        (Real.sqrt (∑ j : Fin d, (x' j - y' j) ^ 2)) ^ beta :=
      hquotNum.trans (mul_le_mul_of_nonneg_right hVbetaBoundC
        (Real.rpow_nonneg he'.le beta))
    have hvalue : |U x - U y| = |V x' - V y'| := by
      change |U x - U y| =
        |(U (z + r • x') - c) - (U (z + r • y') - c)|
      rw [normalizedBoundaryPoint_reconstruct z hr x,
        normalizedBoundaryPoint_reconstruct z hr y]
      exact congrArg abs (by linarith only [])
    have hdistance := normalizedBoundaryPoint_euclideanDistance z hr x y
    have hdenom : (r * Real.sqrt (∑ j : Fin d, (x' j - y' j) ^ 2)) ^ beta =
        r ^ beta * (Real.sqrt (∑ j : Fin d, (x' j - y' j) ^ 2)) ^ beta :=
      Real.mul_rpow hr.le (Real.sqrt_nonneg _)
    rw [hdistance, hdenom, hvalue]
    apply (div_le_div_iff₀
      (mul_pos hpowPos (Real.rpow_pos_of_pos he' beta)) hpowPos).2
    calc
      |V x' - V y'| * r ^ beta ≤
          (C * (Real.sqrt (∑ j : Fin d, (x' j - y' j) ^ 2)) ^ beta) * r ^ beta :=
        mul_le_mul_of_nonneg_right hquotNumC hpowPos.le
      _ = C * (r ^ beta *
          (Real.sqrt (∑ j : Fin d, (x' j - y' j) ^ 2)) ^ beta) := by
        rw [mul_assoc, mul_comm _ (r ^ beta)]
  have hphys : IsHolderOn beta (frontier (Metric.ball z (r / 2))) U := by
    change BddAbove (holderRatioSet beta (frontier (Metric.ball z (r / 2))) U)
    exact ⟨C / r ^ beta, hratio⟩
  have hsem : holderSeminorm beta (frontier (Metric.ball z (r / 2))) U ≤ C / r ^ beta :=
    Real.sSup_le hratio (div_nonneg hCnonneg (Real.rpow_nonneg hr.le _))
  refine ⟨hphys, ?_⟩
  calc
    r ^ beta * holderSeminorm beta (frontier (Metric.ball z (r / 2))) U ≤
        r ^ beta * (C / r ^ beta) :=
      mul_le_mul_of_nonneg_left hsem (Real.rpow_nonneg hr.le _)
    _ = C := by
      rw [div_eq_mul_inv]
      calc
        r ^ beta * (C * (r ^ beta)⁻¹) = r ^ beta * ((r ^ beta)⁻¹ * C) := by
          rw [mul_comm C]
        _ = (r ^ beta * (r ^ beta)⁻¹) * C := by rw [← mul_assoc]
        _ = C := by rw [mul_inv_cancel₀ (ne_of_gt hpowPos), one_mul]

end SubdiffusiveProcess
