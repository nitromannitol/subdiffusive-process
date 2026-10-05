module

public import Mathlib
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.CubeTrace.Scale

@[expose] public section

/-!
# Cube trace extension: gluing lemmas for the final assembly
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal ContDiff Topology Classical
open _root_.SubdiffusiveProcess.EllipticRegularity
noncomputable section
namespace SubdiffusiveProcess.CubeTrace

variable {d : ℕ}

/-- From `IsHolderOn` and the supremum definition of `holderSeminorm` to the pointwise Hölder bound. -/
theorem holder_pointwise {S : Set (SpatialCoordinates d)} {β : ℝ} (hβ : 0 < β)
    {G : SpatialCoordinates d → ℝ} (hG : IsHolderOn β S G) :
    0 ≤ holderSeminorm β S G ∧ ∀ x ∈ S, ∀ y ∈ S,
      |G x - G y| ≤ holderSeminorm β S G * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ β := by
  have hnn : 0 ≤ holderSeminorm β S G := by
    refine Real.sSup_nonneg ?_
    rintro v ⟨x, _, y, _, _, rfl⟩
    exact div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  refine ⟨hnn, ?_⟩
  intro x hx y hy
  by_cases hxy : x = y
  · subst hxy
    simp [Real.zero_rpow hβ.ne']
  · have hsum : 0 < ∑ j : Fin d, (x j - y j) ^ 2 := by
      by_contra hle
      have h0 : ∑ j : Fin d, (x j - y j) ^ 2 = 0 :=
        le_antisymm (not_lt.1 hle) (Finset.sum_nonneg fun j _ => sq_nonneg _)
      apply hxy
      funext j
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (x j - y j))).1 h0 j
        (Finset.mem_univ j)
      nlinarith [sq_nonneg (x j - y j)]
    have hr : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := Real.sqrt_pos.2 hsum
    have hrp : 0 < (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ β := Real.rpow_pos_of_pos hr β
    have hmem : |G x - G y| / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ β ∈
        holderRatioSet β S G := ⟨x, hx, y, hy, hxy, rfl⟩
    have hle : |G x - G y| / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ β ≤
        holderSeminorm β S G := le_csSup hG hmem
    rw [div_le_iff₀ hrp] at hle
    exact hle

/-- The sup-norm Hölder bound with the constant `H · d^{β/2}`. -/
theorem holder_sup_norm {S : Set (SpatialCoordinates d)} {β : ℝ} (hβ : 0 < β)
    {G : SpatialCoordinates d → ℝ} (hG : IsHolderOn β S G) :
    ∀ x ∈ S, ∀ y ∈ S,
      |G x - G y| ≤ (holderSeminorm β S G * (d : ℝ) ^ (β / 2)) * dist x y ^ β := by
  obtain ⟨hnn, hp⟩ := holder_pointwise hβ hG
  intro x hx y hy
  refine (hp x hx y hy).trans ?_
  have h1 : (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ β ≤
      (Real.sqrt (d : ℝ) * ‖x - y‖) ^ β :=
    Real.rpow_le_rpow (Real.sqrt_nonneg _) (euclid_le_sqrt_mul_norm x y) hβ.le
  have h2 : (Real.sqrt (d : ℝ) * ‖x - y‖) ^ β = (d : ℝ) ^ (β / 2) * ‖x - y‖ ^ β := by
    rw [Real.mul_rpow (Real.sqrt_nonneg _) (norm_nonneg _), Real.sqrt_eq_rpow,
      ← Real.rpow_mul (Nat.cast_nonneg d)]
    congr 2
    ring
  rw [dist_eq_norm, mul_assoc, ← h2]
  exact mul_le_mul_of_nonneg_left h1 hnn

/-- A globally Hölder function is bounded on the cube. -/
theorem holder_bounded_on_ctQ {G : SpatialCoordinates d → ℝ} {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 < β)
    (hG : ∀ x y, |G x - G y| ≤ K * ‖x - y‖ ^ β) (z : SpatialCoordinates d) :
    ∃ B : ℝ, ∀ x ∈ ctQ z, |G x| ≤ B := by
  refine ⟨|G z| + K, fun x hx => ?_⟩
  have h1 : ‖x - z‖ ^ β ≤ 1 := by
    refine Real.rpow_le_one (norm_nonneg _) ?_ hβ.le
    have := mem_ball_iff_norm.1 hx
    linarith
  calc |G x| = |G z + (G x - G z)| := by ring_nf
    _ ≤ |G z| + |G x - G z| := abs_add_le _ _
    _ ≤ |G z| + K * ‖x - z‖ ^ β := by gcongr; exact hG x z
    _ ≤ |G z| + K := by
        have := mul_le_mul_of_nonneg_left h1 hK
        linarith

/-- Gluing `b` inside the cube to `G` outside gives a continuous function when `b - G → 0` at the
boundary like a power of the scale weight. -/
theorem glue_continuous [NeZero d] {z : SpatialCoordinates d} {b G : SpatialCoordinates d → ℝ}
    {C β : ℝ} (hC : 0 ≤ C) (hβ : 0 < β) (hb : ContinuousOn b (ctQ z)) (hG : Continuous G)
    (hclose : ∀ x ∈ ctQ z, |b x - G x| ≤ C * ctM z x ^ β) :
    Continuous (fun x => if x ∈ ctQ z then b x else G x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ ctQ z
  · have heq : (fun y => if y ∈ ctQ z then b y else G y) =ᶠ[𝓝 x] b := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      simp [hy]
    exact (hb.continuousAt (isOpen_ball.mem_nhds hx)).congr heq.symm
  · obtain ⟨i, hi⟩ : ∃ i, 1 / 2 ≤ |x i - z i| := by
      by_contra hcon
      push Not at hcon
      apply hx
      rw [mem_ball_iff_norm]
      exact (pi_norm_lt_iff (by norm_num)).2 fun i => by simpa [Real.norm_eq_abs] using hcon i
    have hui : ctU z x i ≤ 0 := by
      unfold ctU
      nlinarith [sq_abs (x i - z i), abs_nonneg (x i - z i)]
    have hcont : Continuous (fun y => C * (max (ctU z y i) 0) ^ β) :=
      continuous_const.mul (((continuous_ctU z i).max continuous_const).rpow_const
        (fun _ => Or.inr hβ.le))
    have hval : C * (max (ctU z x i) 0) ^ β = 0 := by
      rw [max_eq_right hui, Real.zero_rpow hβ.ne', mul_zero]
    have hlim : Tendsto (fun y => C * (max (ctU z y i) 0) ^ β) (𝓝 x) (𝓝 0) := by
      have := hcont.tendsto x
      rwa [hval] at this
    have hdiff : Tendsto (fun y => (if y ∈ ctQ z then b y else G y) - G y) (𝓝 x) (𝓝 0) := by
      refine squeeze_zero_norm' (Eventually.of_forall fun y => ?_) hlim
      by_cases hy : y ∈ ctQ z
      · rw [ite_eq_left hy, Real.norm_eq_abs]
        refine (hclose y hy).trans ?_
        have hm := ctM_pos hy
        have hle : ctM z y ≤ max (ctU z y i) 0 := (ctM_le_ctU z y i).trans (le_max_left _ _)
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hm.le hle hβ.le) hC
      · rw [ite_eq_right hy, sub_self, norm_zero]
        exact mul_nonneg hC (Real.rpow_nonneg (le_max_right _ _) _)
    have hsum := hdiff.add hG.continuousAt.tendsto
    have hUx : (if x ∈ ctQ z then b x else G x) = G x := ite_eq_right hx
    show Tendsto _ (𝓝 x) (𝓝 (if x ∈ ctQ z then b x else G x))
    rw [hUx]
    simpa using hsum

/-- The frontier of the open cube is disjoint from it. -/
theorem frontier_ctQ_disjoint (z : SpatialCoordinates d) :
    ∀ x ∈ frontier (ctQ z), x ∉ ctQ z := by
  intro x hx
  rw [isOpen_ball.frontier_eq] at hx
  exact hx.2

end SubdiffusiveProcess.CubeTrace
