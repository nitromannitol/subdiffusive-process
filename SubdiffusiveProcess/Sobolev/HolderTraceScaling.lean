module

public import SubdiffusiveProcess.Sobolev.GoodextHolderLimit

@[expose] public section

/-! Hölder trace scaling on contained cube boundaries.
These estimates retain the concrete boundary containment and the stronger
Hölder hypothesis; they do not construct any form-domain extension.
-/

open Set MeasureTheory
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology

noncomputable section
namespace SubdiffusiveProcess

/-- The Hölder seminorm is nonnegative, including when the ratio set is empty. -/
theorem holderSeminorm_nonneg {d : ℕ} (alpha : ℝ) (S : Set (SpatialCoordinates d))
    (u : SpatialCoordinates d → ℝ) : 0 ≤ holderSeminorm alpha S u := by
  apply Real.sSup_nonneg
  rintro v ⟨x, hx, y, hy, hxy, rfl⟩
  exact div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)

/-- A nonzero Euclidean difference has positive length. -/
theorem sqrt_sum_sq_sub_pos {d : ℕ} {x y : SpatialCoordinates d} (hxy : x ≠ y) :
    0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
  obtain ⟨j, hj⟩ : ∃ j : Fin d, x j ≠ y j := by
    by_contra! hall
    exact hxy (funext hall)
  have hsq : 0 < (x j - y j) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hj)
  have hsum : (x j - y j) ^ 2 ≤ ∑ i : Fin d, (x i - y i) ^ 2 :=
    Finset.single_le_sum (f := fun i : Fin d => (x i - y i) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  exact Real.sqrt_pos.mpr (hsq.trans_le hsum)

/-- A stronger Hölder seminorm controls a weaker one on a set of bounded Euclidean diameter. -/
theorem holderSeminorm_le_of_diameter
    {d : ℕ} {S T : Set (SpatialCoordinates d)} {u : SpatialCoordinates d → ℝ}
    {alpha beta D : ℝ} (hsub : T ⊆ S) (hba : beta ≤ alpha)
    (hD : 0 ≤ D) (hu : IsHolderOn alpha S u)
    (hdiam : ∀ x ∈ T, ∀ y ∈ T,
      Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ D) :
    IsHolderOn beta T u ∧
      holderSeminorm beta T u ≤ holderSeminorm alpha S u * D ^ (alpha - beta) := by
  have hratio : ∀ v ∈ holderRatioSet beta T u,
      v ≤ holderSeminorm alpha S u * D ^ (alpha - beta) := by
    rintro v ⟨x, hx, y, hy, hxy, rfl⟩
    let e := Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)
    have he : 0 < e := sqrt_sum_sq_sub_pos hxy
    have hq : |u x - u y| / e ^ alpha ≤ holderSeminorm alpha S u :=
      le_csSup hu ⟨x, hsub hx, y, hsub hy, hxy, rfl⟩
    have hdif : |u x - u y| ≤ holderSeminorm alpha S u * e ^ alpha :=
      (div_le_iff₀ (Real.rpow_pos_of_pos he _)).mp hq
    calc
      |u x - u y| / e ^ beta ≤ (holderSeminorm alpha S u * e ^ alpha) / e ^ beta :=
        div_le_div_of_nonneg_right hdif (Real.rpow_nonneg he.le _)
      _ = holderSeminorm alpha S u * e ^ (alpha - beta) := by
        rw [Real.rpow_sub he]
        ring
      _ ≤ holderSeminorm alpha S u * D ^ (alpha - beta) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow he.le (hdiam x hx y hy) (sub_nonneg.mpr hba))
          (holderSeminorm_nonneg _ _ _)
  exact ⟨⟨_, hratio⟩, Real.sSup_le hratio
    (mul_nonneg (holderSeminorm_nonneg _ _ _) (Real.rpow_nonneg hD _))⟩

/-- A cube frontier has Euclidean diameter at most square-root dimension times its side. -/
theorem euclidean_frontier_diameter_le {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    {x y : SpatialCoordinates d}
    (hx : x ∈ frontier (Metric.ball z (r / 2)))
    (hy : y ∈ frontier (Metric.ball z (r / 2))) :
    Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt d * r := by
  have hx' : dist x z = r / 2 := Metric.frontier_ball_subset_sphere hx
  have hy' : dist y z = r / 2 := Metric.frontier_ball_subset_sphere hy
  have hd : dist x y ≤ r := by
    calc
      dist x y ≤ dist x z + dist z y := dist_triangle _ _ _
      _ = r := by rw [hx', dist_comm z y, hy']; ring
  exact (_root_.SubdiffusiveProcess.Paper.aux_lem_goodext_euclid_le x y).trans
    (mul_le_mul_of_nonneg_left hd (Real.sqrt_nonneg _))

/-- A global Hölder bound gives the correctly scaled weaker trace bound on every contained cube. -/
theorem scaled_holderSeminorm_frontier_le
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    {S : Set (SpatialCoordinates d)} {u : SpatialCoordinates d → ℝ}
    {alpha beta : ℝ} (hba : beta ≤ alpha)
    (hsub : frontier (Metric.ball z (r / 2)) ⊆ S) (hu : IsHolderOn alpha S u) :
    IsHolderOn beta (frontier (Metric.ball z (r / 2))) u ∧
      r ^ beta * holderSeminorm beta (frontier (Metric.ball z (r / 2))) u ≤
        (Real.sqrt d) ^ (alpha - beta) * holderSeminorm alpha S u * r ^ alpha := by
  obtain ⟨hh, hb⟩ := holderSeminorm_le_of_diameter hsub hba
    (mul_nonneg (Real.sqrt_nonneg _) hr.le) hu (fun _ hx _ hy =>
      euclidean_frontier_diameter_le z r hx hy)
  refine ⟨hh, (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hr.le _)).trans_eq ?_⟩
  rw [Real.mul_rpow (Real.sqrt_nonneg _) hr.le]
  calc
    r ^ beta * (holderSeminorm alpha S u * ((Real.sqrt d) ^ (alpha - beta) *
        r ^ (alpha - beta))) =
        (Real.sqrt d) ^ (alpha - beta) * holderSeminorm alpha S u *
          (r ^ beta * r ^ (alpha - beta)) := by ring
    _ = (Real.sqrt d) ^ (alpha - beta) * holderSeminorm alpha S u * r ^ alpha := by
      rw [← Real.rpow_add hr]
      congr 2
      ring

/-- The trace estimate and a crude inverse-power coefficient give the arbitrary-cell exponent. -/
theorem trace_response_power_bound
    {d : ℕ} {alpha eta C K r trace energy : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C) (hK : 0 ≤ K) (htrace : 0 ≤ trace)
    (htraceBound : trace ≤ K * r ^ alpha)
    (henergy : energy ≤ C * r ^ ((d : ℝ) - 2 - eta) * trace ^ 2) :
    energy ≤ (C * K ^ 2) * r ^ ((d : ℝ) - 2 + 2 * alpha - eta) := by
  have ht : trace ^ 2 ≤ (K * r ^ alpha) ^ 2 :=
    (sq_le_sq₀ htrace (mul_nonneg hK (Real.rpow_nonneg hr.le _))).mpr htraceBound
  refine henergy.trans ((mul_le_mul_of_nonneg_left ht
    (mul_nonneg hC (Real.rpow_nonneg hr.le _))).trans_eq ?_)
  have hp : (r ^ alpha) ^ 2 = r ^ (alpha * (2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    norm_num
  rw [mul_pow, hp]
  calc
    C * r ^ ((d : ℝ) - 2 - eta) * (K ^ 2 * r ^ (alpha * (2 : ℝ))) =
        (C * K ^ 2) * (r ^ ((d : ℝ) - 2 - eta) * r ^ (alpha * 2)) := by ring
    _ = (C * K ^ 2) * r ^ ((d : ℝ) - 2 + 2 * alpha - eta) := by
      rw [← Real.rpow_add hr]
      congr 2
      ring

end SubdiffusiveProcess
