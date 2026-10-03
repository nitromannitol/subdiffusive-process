module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section11.SubunitHarmonicLipschitzIteration

@[expose] public section

/-! Finite convex chaining and the geometry and L2 normalization of localization balls. -/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section11.HarmonicLipschitz
open MeasureTheory Homogenization Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic
noncomputable section

open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
theorem euclidean_segment_step {d : ℕ} (x y : Vec d) (N k : ℕ) :
 euclideanNorm ((x + ((k:ℝ)/N) • (y-x)) -
 (x + (((k:ℝ)+1)/N) • (y-x))) = (1/(N:ℝ))*euclideanNorm (x-y) := by
  have hN : (0:ℝ) ≤ 1/(N:ℝ) := by positivity
  have h : (x + ((k:ℝ)/N) • (y-x)) - (x + (((k:ℝ)+1)/N) • (y-x))
      = (((k:ℝ)/N) - (((k:ℝ)+1)/N)) • (y-x) := by
    rw [add_sub_add_left_eq_sub, sub_smul]
  rw [h, euclideanNorm_smul]
  have hc : ((k:ℝ)/N - (((k:ℝ)+1)/N)) = -(1/(N:ℝ)) := by
    ring
  rw [hc, abs_neg, abs_of_nonneg hN]
  rw [← euclideanNorm_neg, neg_sub]

theorem abs_sub_le_of_uniform_local {d : ℕ} {W : Set (Vec d)} {f : Vec d → ℝ}
 {R K : ℝ} (hW : Convex ℝ W) (hR : 0 < R)
 (hloc : ∀ x ∈ W, ∀ y ∈ W, euclideanNorm (x-y) < R →
 |f x-f y| ≤ K*euclideanNorm (x-y)) {x y : Vec d} (hx : x∈W) (hy : y∈W) :
 |f x-f y| ≤ K*euclideanNorm (x-y) := by
  by_cases hlt : euclideanNorm (x - y) < R
  · exact hloc x hx y hy hlt
  have hApos : 0 < euclideanNorm (x - y) :=
    lt_of_lt_of_le hR (le_of_not_gt hlt)
  obtain ⟨N, hN⟩ := exists_nat_gt (euclideanNorm (x - y) / R)
  have hNpos : 0 < (N:ℝ) := lt_trans (div_pos hApos hR) hN
  have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNpos
  have hA_lt : euclideanNorm (x - y) < (N:ℝ) * R := (div_lt_iff₀ hR).mp hN
  have hstep_lt : ∀ k : ℕ, k < N →
      (1/(N:ℝ)) * euclideanNorm (x - y) < R := by
    intro k _
    have h1 : euclideanNorm (x - y) / (N:ℝ) < R := by
      rw [div_lt_iff₀ hNpos]
      linarith [mul_comm (N:ℝ) R]
    have h2 : (1/(N:ℝ)) * euclideanNorm (x - y)
        = euclideanNorm (x - y) / (N:ℝ) := by
      field_simp
    rw [h2]; exact h1
  have hmem : ∀ k ≤ N, x + ((k:ℝ)/N) • (y - x) ∈ W := by
    intro k hk
    have hkle : (k:ℝ) ≤ (N:ℝ) := Nat.cast_le.mpr hk
    have hdiv1 : (k:ℝ)/N ≤ 1 := (div_le_one hNpos).mpr hkle
    have hdiv0 : 0 ≤ (k:ℝ)/N := div_nonneg (Nat.cast_nonneg _) hNpos.le
    exact Convex.add_smul_sub_mem hW hx hy ⟨hdiv0, hdiv1⟩
  have hstep : ∀ k < N,
      euclideanNorm ((x + ((k:ℝ)/N) • (y - x))
        - (x + ((k+1:ℝ)/N) • (y - x)))
        = (1/(N:ℝ)) * euclideanNorm (x - y) := by
    intro k _; exact euclidean_segment_step x y N k
  have hind : ∀ k ≤ N, |f x - f (x + ((k:ℝ)/N) • (y - x))| ≤
      (k:ℝ) * (K * ((1/(N:ℝ)) * euclideanNorm (x - y))) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp
    | succ n ih =>
      intro hk
      have hnN : n < N := Nat.lt_of_succ_le hk
      have hpn := hmem n (Nat.le_of_lt hnN)
      have hpn1 := hmem (n+1) hk
      simp only [Nat.cast_add, Nat.cast_one] at hpn1 ⊢
      have hlocn := hloc (x + ((n:ℝ)/N) • (y - x)) hpn
        (x + ((n+1:ℝ)/N) • (y - x)) hpn1
        (by rw [hstep n hnN]; exact hstep_lt n hnN)
      rw [hstep n hnN] at hlocn
      calc |f x - f (x + ((n+1:ℝ)/N) • (y - x))|
          ≤ |f x - f (x + ((n:ℝ)/N) • (y - x))|
            + |f (x + ((n:ℝ)/N) • (y - x))
               - f (x + ((n+1:ℝ)/N) • (y - x))| :=
        abs_sub_le _ _ _
        _ ≤ (n:ℝ) * (K * ((1/(N:ℝ)) * euclideanNorm (x - y)))
            + K * ((1/(N:ℝ)) * euclideanNorm (x - y)) :=
        add_le_add (ih (Nat.le_of_lt hnN)) hlocn
        _ = ((n+1:ℝ)) * (K * ((1/(N:ℝ)) * euclideanNorm (x - y))) := by
            ring
  have hpN : x + ((N:ℝ)/N) • (y - x) = y := by
    rw [div_self hNne, one_smul]; abel
  have hcancel : (N:ℝ) * (K * ((1/(N:ℝ)) * euclideanNorm (x - y)))
      = K * euclideanNorm (x - y) := by
    field_simp
  have hfin := hind N le_rfl
  rw [hpN] at hfin
  rw [hcancel] at hfin
  exact hfin

theorem closedBall_subset_cubeSet_of_mem_middleHalf {d : ℕ}
  {U : SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.Cube d} {x : Vec d} {R : ℝ}
  (hU : 0 < U.2) (hR : R ≤ U.2/8)
  (hx : x ∈ SubdiffusiveProcess.Section9.centeredAxisCube U.1 (U.2/2)) :
  Metric.closedBall x R ⊆ SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet U := by
  intro y hy
  rw [Metric.mem_closedBall, dist_eq_norm] at hy
  apply SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.mem_centeredAxisCube.mpr
  intro i
  have hcoord := norm_le_pi_norm (y - x) i
  simp only [Pi.sub_apply, Real.norm_eq_abs] at hcoord
  have h1 : |y i - x i| ≤ R := hcoord.trans hy
  have h2 := SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.mem_centeredAxisCube.mp hx i
  have h3 := abs_sub_le (y i) (x i) (U.1 i)
  linarith

theorem normalizedL2On_ball_le_cube {d : ℕ} [NeZero d]
 {U : SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.Cube d} (hU : 0 < U.2)
 {x : Vec d} {f R : ℝ} (hf : 0 < f) (hR : R = U.2*f)
 (hsub : euclideanBall x R ⊆ SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet U)
 {h : Vec d → ℝ} (hmem : MemLp h 2 (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet U))) :
 normalizedL2On (euclideanBall x R)
 (fun y => h y - averageOn (SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet U) h) ≤
 Real.sqrt (((volume (smallContrastUnitBall d)).toReal*f^d)⁻¹) *
 normalizedL2On (SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet U)
 (fun y => h y - averageOn (SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet U) h) := by
  -- Open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube for cubeSet.
  open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube in
  -- hQtop:volume(cubeSet U)≠⊤
  have hQtop : volume (cubeSet U) ≠ ⊤ :=
    volume_cubeSet_ne_top (B := U)
  -- Finite measure instance on the restricted measure.
  have : IsFiniteMeasure (volume.restrict (cubeSet U)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hQtop⟩
  -- hdiff:MemLp(fun y=>h y-averageOn(cubeSet U)h)2(volume.restrict(cubeSet U))
  have hdiff : MemLp (fun y => h y - averageOn (cubeSet U) h) 2
      (volume.restrict (cubeSet U)) := hmem.sub (memLp_const _)
  -- hQpos:0<(volume(cubeSet U)).toReal
  have hQpos : 0 < (volume (cubeSet U)).toReal := by
    rw [volume_cubeSet_toReal hU.le]; positivity
  -- hRpos:0<R
  have hRpos : 0 < R := by rw [hR]; positivity
  -- hBallpos:0<(volume(euclideanBall x R)).toReal
  have hBallpos : 0 < (volume (euclideanBall x R)).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (Homogenization.Book.Ch01.volume_euclideanBall_toReal_ne_zero x hRpos))
  -- Apply the subset Lipschitz bound, then rewrite the volume ratio.
  have hb := Section6Iteration.normalizedL2On_le_of_subset hsub hQpos hBallpos
    hdiff.integrable_sq
  rw [interior_volumeRatio hU x hf hR] at hb
  exact hb
end
end SubdiffusiveProcess.CoarseGrainingVocab.Section11.HarmonicLipschitz
