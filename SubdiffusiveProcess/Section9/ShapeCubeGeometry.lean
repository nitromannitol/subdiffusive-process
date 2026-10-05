
module

public import Mathlib.Topology.Algebra.Order.Archimedean

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.CubeMoments
public import Homogenization.Sobolev.Foundations.Cutoff.Euclidean

@[expose] public section

/-! # One-cube geometry for Section 9 shape transfers -/

namespace SubdiffusiveProcess.Section9

open Filter MeasureTheory Set Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration

noncomputable section

/-- The corner representation of the axis cube centered at `x`. -/
def centeredAxisCube {d : ℕ} (x : Vec d) (L : ℝ) : Set (Vec d) :=
  axisCube (fun i ↦ x i - L / 2) L

theorem euclideanBall_subset_centeredAxisCube {d m J : ℕ} (x : Vec d)
    (hJ : 2 ≤ (3 : ℝ) ^ J) :
    euclideanBall x ((3 : ℝ) ^ m) ⊆ centeredAxisCube x ((3 : ℝ) ^ (m + J)) := by
  intro y hy
  have hr : 0 < (3 : ℝ) ^ m := pow_pos (by norm_num) _
  have hcoord := euclideanBall_subset_metricBall hr hy
  rw [Metric.mem_ball, dist_pi_lt_iff hr] at hcoord
  intro i hi
  have hi' : |y i - x i| < (3 : ℝ) ^ m := by
    simpa only [Real.dist_eq] using hcoord i
  have hscale : 2 * (3 : ℝ) ^ m ≤ (3 : ℝ) ^ (m + J) := by
    rw [pow_add]
    nlinarith [mul_le_mul_of_nonneg_left hJ
      (show 0 ≤ (3 : ℝ) ^ m by positivity)]
  dsimp only [centeredAxisCube, axisCube]
  change x i - (3 : ℝ) ^ (m + J) / 2 < y i ∧
    y i < x i - (3 : ℝ) ^ (m + J) / 2 + (3 : ℝ) ^ (m + J)
  rcases abs_lt.mp hi' with ⟨hi₁, hi₂⟩
  constructor <;> nlinarith

theorem centeredAxisCube_subset_euclideanBall {d m J : ℕ} [NeZero d]
    (x : Vec d) (hmJ : J ≤ m)
    (hJ : Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-((J : ℤ))) ≤ 2) :
    centeredAxisCube x ((3 : ℝ) ^ (m - J)) ⊆ euclideanBall x ((3 : ℝ) ^ m) := by
  intro y hy
  have hside : 0 < (3 : ℝ) ^ (m - J) := pow_pos (by norm_num) _
  have hcoord : ∀ i : Fin d, |y i - x i| < (3 : ℝ) ^ (m - J) / 2 := by
    intro i
    have hi := hy i (Set.mem_univ i)
    dsimp only [centeredAxisCube, axisCube] at hi
    simp only [Set.mem_Ioo] at hi
    rw [abs_lt]
    constructor <;> linarith
  change euclideanSqDist y x < ((3 : ℝ) ^ m) ^ 2
  unfold euclideanSqDist vecNormSq vecDot
  have hsum : (∑ i : Fin d, (y - x) i * (y - x) i) <
      ∑ _i : Fin d, ((3 : ℝ) ^ (m - J) / 2) ^ 2 := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact Finset.univ_nonempty
    · intro i hi
      have hi' := hcoord i
      rw [Pi.sub_apply, ← sq_abs]
      have hs := (sq_lt_sq₀ (abs_nonneg _) (by positivity)).mpr hi'
      rw [abs_of_pos (by positivity : 0 < (3 : ℝ) ^ (m - J) / 2)]
      nlinarith [sq_abs (y i - x i)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hsqrt : Real.sqrt (d : ℝ) ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg d)
  have hpow : (3 : ℝ) ^ m = (3 : ℝ) ^ (m - J) * (3 : ℝ) ^ J := by
    rw [← pow_add, Nat.sub_add_cancel hmJ]
  have hJ' : Real.sqrt (d : ℝ) ≤ 2 * (3 : ℝ) ^ J := by
    rw [zpow_neg, zpow_natCast] at hJ
    exact (div_le_iff₀ (pow_pos (by norm_num) J)).mp hJ
  have hnonneg : 0 ≤ Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(J : ℤ)) :=
    mul_nonneg (Real.sqrt_nonneg _) (zpow_nonneg (by norm_num) _)
  nlinarith [sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity : 0 ≤ 2 * (3 : ℝ) ^ J) |>.mpr hJ',
    pow_pos (by norm_num : (0 : ℝ) < 3) m,
    pow_pos (by norm_num : (0 : ℝ) < 3) (m - J), hpow]

theorem axisCube_concentric_small_subset_large {d : ℕ} (z : Vec d)
    {r R : ℝ} (hrR : r ≤ R) :
    axisCube z r ⊆ axisCube (fun i ↦ z i + r / 2 - R / 2) R := by
  intro y hy i hi
  have h := hy i (Set.mem_univ i)
  change z i < y i ∧ y i < z i + r at h
  change z i + r / 2 - R / 2 < y i ∧ y i < z i + r / 2 - R / 2 + R
  constructor <;> linarith

theorem axisCube_subset_concentric_large {d : ℕ} (z : Vec d)
    {r R : ℝ} (hrR : r ≤ R) :
    axisCube (fun i ↦ z i + R / 2 - r / 2) r ⊆ axisCube z R := by
  intro y hy i hi
  have h := hy i (Set.mem_univ i)
  change z i + R / 2 - r / 2 < y i ∧ y i < z i + R / 2 - r / 2 + r at h
  change z i < y i ∧ y i < z i + R
  constructor <;> linarith

theorem volume_centeredAxisCube_toReal {d : ℕ} (x : Vec d) {L : ℝ}
    (hL : 0 ≤ L) : (volume (centeredAxisCube x L)).toReal = L ^ d := by
  exact volume_axisCube_toReal _ hL

theorem axisCube_scaled_volume_ratio {d m J : ℕ} (z : Vec d) (r : ℝ)
    (hr : 0 < r) :
    (volume (axisCube z ((3 : ℝ) ^ (m + J)))).toReal /
        (volume (axisCube z ((3 : ℝ) ^ m * r))).toReal =
      (3 : ℝ) ^ (d * J) / r ^ d := by
  rw [volume_axisCube_toReal _ (by positivity), volume_axisCube_toReal _ (by positivity),
    pow_mul, pow_add, mul_pow]
  field_simp [hr.ne']
  ring

theorem axisCube_scaled_volume_ratio_small {d m J : ℕ} (z : Vec d) (r : ℝ)
    (hr : 0 < r) (hJm : J ≤ m) :
    (volume (axisCube z ((3 : ℝ) ^ m * r))).toReal /
        (volume (axisCube z ((3 : ℝ) ^ (m - J)))).toReal =
      r ^ d * (3 : ℝ) ^ (d * J) := by
  rw [volume_axisCube_toReal _ (by positivity), volume_axisCube_toReal _ (by positivity),
    mul_pow, pow_mul]
  have hpow : (3 : ℝ) ^ m = (3 : ℝ) ^ (m - J) * (3 : ℝ) ^ J := by
    rw [← pow_add, Nat.sub_add_cancel hJm]
  rw [hpow, mul_pow]
  field_simp [hr.ne', pow_ne_zero _ (by norm_num : (3 : ℝ) ≠ 0)]
  ring

/-- A finite positive-side family admits one enlargement depth controlling side,
inverse side, displacement from the coefficient anchor, and the Euclidean-ball
inner/outer requirements. -/
theorem exists_shapeCubeDepth {d : ℕ}
    (S : Finset {q : Vec d × ℝ // 0 < q.2}) :
    ∃ J : ℕ,
      2 ≤ (3 : ℝ) ^ J ∧
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(J : ℤ)) ≤ 2 ∧
      ∀ Q ∈ S, Q.val.2 ≤ (3 : ℝ) ^ J ∧
        (3 : ℝ) ^ (-(J : ℤ)) ≤ Q.val.2 ∧
        ∀ i, |Q.val.1 i| < (3 : ℝ) ^ J ∧
          |Q.val.1 i + Q.val.2| < (3 : ℝ) ^ J := by
  let B : ℝ := 2 + Real.sqrt (d : ℝ) / 2 +
    ∑ Q ∈ S, (Q.val.2 + Q.val.2⁻¹ +
      ∑ i : Fin d, (|Q.val.1 i| + |Q.val.1 i + Q.val.2|))
  have hterm0 (Q : {q : Vec d × ℝ // 0 < q.2}) : 0 ≤
      Q.val.2 + Q.val.2⁻¹ + ∑ i : Fin d,
        (|Q.val.1 i| + |Q.val.1 i + Q.val.2|) := by
    have hq := Q.property
    positivity
  have hpow : Tendsto (fun J : ℕ ↦ (3 : ℝ) ^ J) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨J, hJB⟩ := (hpow.eventually (eventually_gt_atTop B)).exists
  refine ⟨J, ?_, ?_, ?_⟩
  · dsimp only [B] at hJB
    have hsqrt : 0 ≤ Real.sqrt (d : ℝ) / 2 := by positivity
    have hsum : 0 ≤ ∑ Q ∈ S, (Q.val.2 + Q.val.2⁻¹ +
        ∑ i : Fin d, (|Q.val.1 i| + |Q.val.1 i + Q.val.2|)) := by
      exact Finset.sum_nonneg fun Q _ ↦ hterm0 Q
    linarith
  · rw [zpow_neg, zpow_natCast]
    have hthree : 0 < (3 : ℝ) ^ J := pow_pos (by norm_num) _
    apply (div_le_iff₀ hthree).mpr
    dsimp only [B] at hJB
    have hsum : 0 ≤ ∑ Q ∈ S, (Q.val.2 + Q.val.2⁻¹ +
        ∑ i : Fin d, (|Q.val.1 i| + |Q.val.1 i + Q.val.2|)) := by
      exact Finset.sum_nonneg fun Q _ ↦ hterm0 Q
    nlinarith [Real.sqrt_nonneg (d : ℝ)]
  · intro Q hQS
    have hterm := Finset.single_le_sum (s := S) (f := fun Q ↦
      Q.val.2 + Q.val.2⁻¹ + ∑ i : Fin d,
        (|Q.val.1 i| + |Q.val.1 i + Q.val.2|))
      (fun R hR ↦ hterm0 R) hQS
    have hQB : Q.val.2 + Q.val.2⁻¹ + ∑ i : Fin d,
        (|Q.val.1 i| + |Q.val.1 i + Q.val.2|) < (3 : ℝ) ^ J := by
      dsimp only [B] at hJB
      have hbase : 0 ≤ 2 + Real.sqrt (d : ℝ) / 2 := by positivity
      linarith
    have hqpos := Q.property
    have hcoords : 0 ≤ ∑ i : Fin d,
        (|Q.val.1 i| + |Q.val.1 i + Q.val.2|) :=
      Finset.sum_nonneg fun i _ ↦ add_nonneg (abs_nonneg _) (abs_nonneg _)
    constructor
    · linarith [inv_pos.mpr hqpos]
    constructor
    · rw [zpow_neg, zpow_natCast]
      have hinv : Q.val.2⁻¹ < (3 : ℝ) ^ J := by
        linarith
      rw [inv_eq_one_div]
      apply (div_le_iff₀ (pow_pos (by norm_num) J)).mpr
      calc
        1 = Q.val.2 * Q.val.2⁻¹ := (mul_inv_cancel₀ hqpos.ne').symm
        _ ≤ Q.val.2 * (3 : ℝ) ^ J :=
          mul_le_mul_of_nonneg_left hinv.le hqpos.le
    · intro i
      have hi := Finset.single_le_sum (s := Finset.univ)
        (f := fun i : Fin d ↦ |Q.val.1 i| + |Q.val.1 i + Q.val.2|)
        (fun _ _ ↦ by positivity) (Finset.mem_univ i)
      constructor <;> linarith [abs_nonneg (Q.val.1 i),
        abs_nonneg (Q.val.1 i + Q.val.2), inv_pos.mpr hqpos]

theorem scaled_axisCube_subset_anchor_closedBall {d m J : ℕ}
    (x q : Vec d) {r : ℝ} (hr : 0 < r)
    (hq : ∀ i, |q i| ≤ (3 : ℝ) ^ J ∧ |q i + r| ≤ (3 : ℝ) ^ J) :
    axisCube (x + (3 : ℝ) ^ m • q) ((3 : ℝ) ^ m * r) ⊆
      Metric.closedBall x ((3 : ℝ) ^ (m + J)) := by
  intro y hy
  rw [Metric.mem_closedBall, dist_pi_le_iff (pow_nonneg (by norm_num) _)]
  intro i
  have hi := hy i (Set.mem_univ i)
  change x i + (3 : ℝ) ^ m * q i < y i ∧
    y i < x i + (3 : ℝ) ^ m * q i + (3 : ℝ) ^ m * r at hi
  rw [Real.dist_eq, abs_le]
  have hp : 0 < (3 : ℝ) ^ m := pow_pos (by norm_num) _
  have hpr : 0 < (3 : ℝ) ^ m * r := mul_pos hp hr
  rw [pow_add]
  rcases hq i with ⟨hq₁, hq₂⟩
  rcases abs_le.mp hq₁ with ⟨hq₁l, hq₁u⟩
  rcases abs_le.mp hq₂ with ⟨hq₂l, hq₂u⟩
  have hlo := mul_le_mul_of_nonneg_left hq₁l hp.le
  have hhi := mul_le_mul_of_nonneg_left hq₂u hp.le
  constructor <;> nlinarith [hpr]

end

end SubdiffusiveProcess.Section9
