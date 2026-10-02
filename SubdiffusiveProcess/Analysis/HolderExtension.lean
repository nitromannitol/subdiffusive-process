import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Scalar Hölder extension on an arbitrary metric space, proved by the
McShane infimum formula. This module makes no Sobolev or energy claim. -/

open Set Filter
open scoped Topology
noncomputable section
namespace SubdiffusiveProcess

/-- Powers at most one preserve the metric triangle inequality. -/
theorem dist_rpow_triangle {X : Type*} [PseudoMetricSpace X]
    {beta : ℝ} (hb : 0 ≤ beta) (hb1 : beta ≤ 1) (x y z : X) :
    dist x z ^ beta ≤ dist x y ^ beta + dist y z ^ beta :=
  (Real.rpow_le_rpow dist_nonneg (dist_triangle x y z) hb).trans
    (Real.rpow_add_le_add_rpow dist_nonneg dist_nonneg hb hb1)

/-- A scalar Hölder function on any subset extends with the same constant. -/
theorem exists_holder_extension {X : Type*} [PseudoMetricSpace X]
    (S : Set X) (f : X → ℝ) (K beta : ℝ) (hK : 0 ≤ K)
    (hb : 0 < beta) (hb1 : beta ≤ 1)
    (hf : ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ K * dist x y ^ beta) :
    ∃ g : X → ℝ, EqOn g f S ∧
      ∀ x y, |g x - g y| ≤ K * dist x y ^ beta := by
  classical
  rcases eq_empty_or_nonempty S with rfl | hs
  · refine ⟨fun _ => 0, eqOn_empty _ _, ?_⟩
    intro x y
    simpa only [sub_self, abs_zero] using
      mul_nonneg hK (Real.rpow_nonneg dist_nonneg beta)
  haveI nonemptyS : Nonempty S := hs.to_subtype
  let g : X → ℝ := fun y => ⨅ x : S, f x + K * dist y x ^ beta
  have hB (y : X) : BddBelow (range fun x : S => f x + K * dist y x ^ beta) := by
    obtain ⟨z, hz⟩ := hs
    refine ⟨f z - K * dist y z ^ beta, ?_⟩
    rintro w ⟨v, rfl⟩
    have hdiff := (le_abs_self (f z - f v)).trans (hf z hz v v.property)
    have htri : dist z v ^ beta ≤ dist y z ^ beta + dist y v ^ beta := by
      simpa only [dist_comm z y] using dist_rpow_triangle hb.le hb1 z y v
    have hmul := mul_le_mul_of_nonneg_left htri hK
    linarith only [hdiff, hmul]
  have heq : EqOn g f S := by
    intro x hx
    apply le_antisymm
    · have h := ciInf_le (hB x) (⟨x, hx⟩ : S)
      simpa only [dist_self, Real.zero_rpow hb.ne', mul_zero, add_zero] using h
    · apply le_ciInf
      intro y
      have h := (le_abs_self (f x - f y)).trans (hf x hx y y.property)
      linarith only [h]
  have hupper (x y : X) : g x - g y ≤ K * dist x y ^ beta := by
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add']
    apply le_ciInf
    intro z
    have hx := ciInf_le (hB x) z
    have htri := dist_rpow_triangle hb.le hb1 x y (z : X)
    have hmul := mul_le_mul_of_nonneg_left htri hK
    linarith only [hx, hmul]
  refine ⟨g, heq, fun x y => abs_sub_le_iff.mpr ⟨hupper x y, ?_⟩⟩
  simpa only [dist_comm y x] using hupper y x

/-- A positive-exponent metric Hölder bound gives continuity. -/
theorem continuous_of_dist_holder_bound {X : Type*} [PseudoMetricSpace X]
    (g : X → ℝ) (K beta : ℝ) (hb : 0 < beta)
    (hg : ∀ x y, |g x - g y| ≤ K * dist x y ^ beta) : Continuous g := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hdist : Tendsto (fun y : X => dist y x) (𝓝 x) (𝓝 0) := by
    have hc : Continuous (fun y : X => dist y x) := continuous_id.dist continuous_const
    simpa only [dist_self] using hc.tendsto x
  have hpow : Tendsto (fun t : ℝ => t ^ beta) (𝓝 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hb.ne'] using
      (Real.continuousAt_rpow_const (0 : ℝ) beta (Or.inr hb.le)).tendsto
  have hlim := (hpow.comp hdist).const_mul K
  have hlim0 : Tendsto (fun y : X => K * dist y x ^ beta) (𝓝 x) (𝓝 0) := by
    simpa only [mul_zero] using hlim
  apply squeeze_zero (fun _ => dist_nonneg) _ hlim0
  intro y
  simpa only [Real.dist_eq] using hg y x

/-- Bounded Hölder data extend while vanishing on any uniformly separated set. -/
theorem exists_holder_extension_zero_on {X : Type*} [PseudoMetricSpace X]
    (S T : Set X) (f : X → ℝ) (K B delta beta : ℝ)
    (hK : 0 ≤ K) (hd : 0 < delta)
    (hb : 0 < beta) (hb1 : beta ≤ 1)
    (hf : ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ K * dist x y ^ beta)
    (hbound : ∀ x ∈ S, |f x| ≤ B)
    (hsep : ∀ x ∈ S, ∀ y ∈ T, delta ≤ dist x y) :
    ∃ (g : X → ℝ) (C : ℝ), 0 ≤ C ∧ Continuous g ∧
      EqOn g f S ∧ (∀ x ∈ T, g x = 0) ∧
      ∀ x y, |g x - g y| ≤ C * dist x y ^ beta := by
  classical
  let C := max K (B / delta ^ beta)
  have hC : 0 ≤ C := hK.trans (le_max_left _ _)
  have hdisj : Disjoint S T := Set.disjoint_left.mpr (by
    intro x hxS hxT
    have h := hsep x hxS x hxT
    rw [dist_self] at h
    exact (not_le_of_gt hd) h)
  let f0 := S.piecewise f (fun _ => 0)
  have hcross (x : X) (hx : x ∈ S) (y : X) (hy : y ∈ T) :
      |f x| ≤ C * dist x y ^ beta := by
    have hdpos : 0 < delta ^ beta := Real.rpow_pos_of_pos hd beta
    have hpow := Real.rpow_le_rpow hd.le (hsep x hx y hy) hb.le
    have hBC : B ≤ C * delta ^ beta := (div_le_iff₀ hdpos).mp (le_max_right _ _)
    exact (hbound x hx).trans (hBC.trans (mul_le_mul_of_nonneg_left hpow hC))
  have hdata : ∀ x ∈ S ∪ T, ∀ y ∈ S ∪ T,
      |f0 x - f0 y| ≤ C * dist x y ^ beta := by
    intro x hx y hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · have h := (hf x hx y hy).trans
        (mul_le_mul_of_nonneg_right (show K ≤ C from le_max_left K (B / delta ^ beta))
          (Real.rpow_nonneg dist_nonneg beta))
      simpa only [f0, Set.piecewise_eq_of_mem S f _ hx, Set.piecewise_eq_of_mem S f _ hy] using h
    · have hyS : y ∉ S := fun hy' => Set.disjoint_left.mp hdisj hy' hy
      simpa only [f0, Set.piecewise_eq_of_mem S f _ hx,
        Set.piecewise_eq_of_notMem S f _ hyS, sub_zero] using hcross x hx y hy
    · have hxS : x ∉ S := fun hx' => Set.disjoint_left.mp hdisj hx' hx
      simpa only [f0, Set.piecewise_eq_of_notMem S f _ hxS,
        Set.piecewise_eq_of_mem S f _ hy, zero_sub, abs_neg, dist_comm x y]
        using hcross y hy x hx
    · have hxS : x ∉ S := fun hx' => Set.disjoint_left.mp hdisj hx' hx
      have hyS : y ∉ S := fun hy' => Set.disjoint_left.mp hdisj hy' hy
      simpa only [f0, Set.piecewise_eq_of_notMem S f _ hxS,
        Set.piecewise_eq_of_notMem S f _ hyS, sub_self, abs_zero]
        using mul_nonneg hC (Real.rpow_nonneg (dist_nonneg (x := x) (y := y)) beta)
  obtain ⟨g, hgf, hg⟩ := exists_holder_extension (S ∪ T) f0 C beta hC hb hb1 hdata
  refine ⟨g, C, hC, continuous_of_dist_holder_bound g C beta hb hg, ?_, ?_, hg⟩
  · intro x hx
    exact (hgf (Or.inl hx)).trans (Set.piecewise_eq_of_mem S f _ hx)
  · intro x hx
    have hxS : x ∉ S := fun hx' => Set.disjoint_left.mp hdisj hx' hx
    exact (hgf (Or.inr hx)).trans (Set.piecewise_eq_of_notMem S f _ hxS)

end SubdiffusiveProcess
