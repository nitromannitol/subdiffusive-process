module

public import SubdiffusiveProcess.Analysis.HolderExtension
public import SubdiffusiveProcess.Sobolev.HolderTraceScaling

@[expose] public section

/-! Concrete scalar Hölder boundary data extend to globally continuous Hölder
functions vanishing on separated boundaries. No form-domain claim is made. -/

open Set MeasureTheory
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology
noncomputable section
namespace SubdiffusiveProcess

/-- Euclidean coordinate distance dominates the supremum distance. -/
theorem dist_le_sqrt_sum_sq_sub {d : ℕ} (x y : SpatialCoordinates d) :
    dist x y ≤ Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
  apply (dist_pi_le_iff (Real.sqrt_nonneg _)).mpr
  intro j
  have h := Real.sqrt_le_sqrt (Finset.single_le_sum
    (f := fun i : Fin d => (x i - y i) ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ j))
  simpa only [Real.sqrt_sq_eq_abs, Real.dist_eq] using h

/-- The concrete Euclidean Hölder seminorm controls supremum-metric increments. -/
theorem dist_holder_bound_of_isHolderOn {d : ℕ} {beta : ℝ}
    (hb : 0 ≤ beta) {S : Set (SpatialCoordinates d)} {f : SpatialCoordinates d → ℝ}
    (hf : IsHolderOn beta S f) :
    ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤
      (holderSeminorm beta S f * (Real.sqrt d) ^ beta) * dist x y ^ beta := by
  intro x hx y hy
  by_cases hxy : x = y
  · subst y
    exact (show |f x - f x| = 0 by rw [sub_self, abs_zero]) ▸
      mul_nonneg (mul_nonneg (holderSeminorm_nonneg _ _ _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _))
        (Real.rpow_nonneg dist_nonneg _)
  have he : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := sqrt_sum_sq_sub_pos hxy
  have hquot : |f x - f y| / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta ≤
      holderSeminorm beta S f := le_csSup hf ⟨x, hx, y, hy, hxy, rfl⟩
  have hdif := (div_le_iff₀ (Real.rpow_pos_of_pos he beta)).mp hquot
  have hpow := Real.rpow_le_rpow he.le (_root_.SubdiffusiveProcess.Paper.aux_lem_goodext_euclid_le x y) hb
  calc
    |f x - f y| ≤ holderSeminorm beta S f * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta := hdif
    _ ≤ holderSeminorm beta S f * (Real.sqrt d * dist x y) ^ beta :=
      mul_le_mul_of_nonneg_left hpow (holderSeminorm_nonneg _ _ _)
    _ = (holderSeminorm beta S f * (Real.sqrt d) ^ beta) * dist x y ^ beta := by
      rw [Real.mul_rpow (Real.sqrt_nonneg _) dist_nonneg]
      ring

/-- A supremum-metric Hölder bound controls the concrete Euclidean seminorm. -/
theorem isHolderOn_of_dist_holder_bound {d : ℕ} (beta K : ℝ)
    (hb : 0 ≤ beta) (hK : 0 ≤ K) (S : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ)
    (hf : ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ K * dist x y ^ beta) :
    IsHolderOn beta S f ∧ holderSeminorm beta S f ≤ K := by
  have hquot : ∀ v ∈ holderRatioSet beta S f, v ≤ K := by
    rintro v ⟨x, hx, y, hy, hxy, rfl⟩
    have he := sqrt_sum_sq_sub_pos hxy
    apply (div_le_iff₀ (Real.rpow_pos_of_pos he beta)).mpr
    exact (hf x hx y hy).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow dist_nonneg (dist_le_sqrt_sum_sq_sub x y) hb) hK)
  exact ⟨⟨K, hquot⟩, Real.sSup_le hquot hK⟩

/-- Compact Hölder boundary data have a global Hölder extension zero on any separated boundary. -/
theorem exists_holder_boundary_extension_zero_on {d : ℕ}
    (S T : Set (SpatialCoordinates d)) (hS : IsCompact S)
    (f : SpatialCoordinates d → ℝ) (hc : ContinuousOn f S)
    (beta : ℝ) (hb : 0 < beta) (hb1 : beta ≤ 1)
    (hf : IsHolderOn beta S f) (delta : ℝ) (hd : 0 < delta)
    (hsep : ∀ x ∈ S, ∀ y ∈ T, delta ≤ dist x y) :
    ∃ g : SpatialCoordinates d → ℝ, Continuous g ∧
      IsHolderOn beta Set.univ g ∧ EqOn g f S ∧ (∀ x ∈ T, g x = 0) := by
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hc
  have hbound : ∀ x ∈ S, |f x| ≤ B := by
    intro x hx
    simpa only [Real.norm_eq_abs] using hB x hx
  let K := holderSeminorm beta S f * (Real.sqrt d) ^ beta
  have hK : 0 ≤ K := mul_nonneg (holderSeminorm_nonneg _ _ _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  obtain ⟨g, C, hC, hgc, hgf, hgT, hg⟩ := exists_holder_extension_zero_on
    S T f K B delta beta hK hd hb hb1 (dist_holder_bound_of_isHolderOn hb.le hf) hbound hsep
  have hgHolder := isHolderOn_of_dist_holder_bound beta C hb.le hC Set.univ g
    (fun x _ y _ => hg x y)
  exact ⟨g, hgc, hgHolder.1, hgf, hgT⟩

/-- Concentric cube frontiers have separation equal to half the side gap. -/
theorem cube_frontier_separation {d : ℕ} (z : SpatialCoordinates d) (r R : ℝ)
    {x y : SpatialCoordinates d}
    (hx : x ∈ frontier (Metric.ball z (r / 2)))
    (hy : y ∈ frontier (Metric.ball z (R / 2))) : (R - r) / 2 ≤ dist x y := by
  have hxrad := Metric.mem_sphere.mp (Metric.frontier_ball_subset_sphere hx)
  have hyrad := Metric.mem_sphere.mp (Metric.frontier_ball_subset_sphere hy)
  have htri := dist_triangle y x z
  rw [hxrad, hyrad, dist_comm y x] at htri
  linarith only [htri]

/-- A Hölder trace on a cube extends continuously to all space and vanishes on a larger concentric cube frontier. -/
theorem exists_holder_concentric_extension {d : ℕ}
    (z : SpatialCoordinates d) (r R : ℝ) (hrR : r < R)
    (f : SpatialCoordinates d → ℝ)
    (hc : ContinuousOn f (frontier (Metric.ball z (r / 2))))
    (beta : ℝ) (hb : 0 < beta) (hb1 : beta ≤ 1)
    (hf : IsHolderOn beta (frontier (Metric.ball z (r / 2))) f) :
    ∃ g : SpatialCoordinates d → ℝ, Continuous g ∧ IsHolderOn beta Set.univ g ∧
      EqOn g f (frontier (Metric.ball z (r / 2))) ∧
      (∀ x ∈ frontier (Metric.ball z (R / 2)), g x = 0) := by
  have hS : IsCompact (frontier (Metric.ball z (r / 2))) :=
    (isCompact_closedBall z (r / 2)).of_isClosed_subset isClosed_frontier (by
      intro x hx
      exact Metric.mem_closedBall.mpr
        (Metric.mem_sphere.mp (Metric.frontier_ball_subset_sphere hx)).le)
  exact exists_holder_boundary_extension_zero_on _ _ hS f hc beta hb hb1 hf
    ((R - r) / 2) (half_pos (sub_pos.mpr hrR))
    (fun _ hx _ hy => cube_frontier_separation z r R hx hy)

end SubdiffusiveProcess
