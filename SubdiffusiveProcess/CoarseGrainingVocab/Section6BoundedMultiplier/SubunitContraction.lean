module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SmallContrastLocalRegularity

@[expose] public section

/-!
# Concentric sub-unit contraction for the bounded-multiplier argument

This module extracts the shrinking-window consequence of the established
small-contrast Schauder theorem.  On a physical ball of radius `rho`, the
canonical representative contracts on concentric sup-norm balls by the
explicit factor `3^(-alpha * n)`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

noncomputable section

variable {d : ℕ}

private theorem euclideanNorm_sub_le_sub_add_sub
    (u v x : Vec d) :
    euclideanNorm (u - v) ≤
      euclideanNorm (u - x) + euclideanNorm (x - v) := by
  rw [euclideanNorm_eq_norm_ofVec, euclideanNorm_eq_norm_ofVec,
    euclideanNorm_eq_norm_ofVec]
  have hsum : HilbertVec.ofVec (u - v) =
      HilbertVec.ofVec (u - x) + HilbertVec.ofVec (x - v) := by
    ext i
    simp
  rw [hsum]
  exact norm_add_le _ _

/-- Literal oscillation is unchanged when two representatives agree on the
set on which the oscillation is taken. -/
theorem oscillationOn_congr_of_eqOn {S : Set (Vec d)} {f g : Vec d → ℝ}
    (hfg : Set.EqOn f g S) :
    oscillationOn S f = oscillationOn S g := by
  unfold oscillationOn
  congr 1
  ext r
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, hx, y, hy, by rw [hfg hx, hfg hy]⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, hx, y, hy, by rw [hfg hx, hfg hy]⟩

/-- A Euclidean Hölder row controls literal oscillation on every concentric
sup-norm ball.  The factor `2*d` is the crude conversion from the project
sup norm to the explicit Euclidean norm. -/
theorem oscillationOn_metricBall_le_of_euclideanHolder [NeZero d]
    {x : Vec d} {r R alpha K : ℝ} {f : Vec d → ℝ}
    (hr : 0 < r) (hrR : (d : ℝ) * r < R)
    (halpha : 0 ≤ alpha) (hK : 0 ≤ K)
    (hholder : EuclideanHolderBoundOn (euclideanBall x R) alpha K f) :
    oscillationOn (Metric.ball x r) f ≤
      K * (2 * (d : ℝ) * r) ^ alpha := by
  unfold oscillationOn
  apply csSup_le
  · exact ⟨0, x, Metric.mem_ball_self hr, x, Metric.mem_ball_self hr, by simp⟩
  · intro q hq
    rcases hq with ⟨u, hu, v, hv, rfl⟩
    have hd0 : 0 < (d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    have hdr0 : 0 < (d : ℝ) * r := mul_pos hd0 hr
    have hsmall : Metric.ball x r ⊆ euclideanBall x ((d : ℝ) * r) :=
      metricBall_subset_euclideanBall_dimension x r
    have hlarge : euclideanBall x ((d : ℝ) * r) ⊆ euclideanBall x R :=
      euclideanBall_subset_euclideanBall hdr0.le hrR
    have huLarge := hlarge (hsmall hu)
    have hvLarge := hlarge (hsmall hv)
    have huDist : euclideanNorm (u - x) < (d : ℝ) * r := by
      have huSq : euclideanNorm (u - x) ^ 2 < ((d : ℝ) * r) ^ 2 := by
        simpa only [euclideanNorm_sq] using! hsmall hu
      exact (sq_lt_sq₀ (euclideanNorm_nonneg _) hdr0.le).mp huSq
    have hvDist : euclideanNorm (x - v) < (d : ℝ) * r := by
      have hvSq : euclideanNorm (v - x) ^ 2 < ((d : ℝ) * r) ^ 2 := by
        simpa only [euclideanNorm_sq] using! hsmall hv
      have hvDist' := (sq_lt_sq₀ (euclideanNorm_nonneg _) hdr0.le).mp hvSq
      simpa only [show x - v = -(v - x) by abel, euclideanNorm_neg] using! hvDist'
    have huv : euclideanNorm (u - v) ≤ 2 * (d : ℝ) * r :=
      (euclideanNorm_sub_le_sub_add_sub u v x).trans (by linarith)
    have hpow : euclideanNorm (u - v) ^ alpha ≤
        (2 * (d : ℝ) * r) ^ alpha :=
      Real.rpow_le_rpow (euclideanNorm_nonneg _) huv halpha
    exact (hholder u huLarge v hvLarge).trans
      (mul_le_mul_of_nonneg_left hpow hK)

/-- The physical small-contrast theorem gives an explicit triadic contraction
on concentric sub-unit balls.  This is the analytic `3^{-alpha n}` leg needed
below scale one; the separate large-scale Campanato input supplies the
starting amplitude in the bounded-multiplier provider. -/
theorem canonicalRepresentative_subunit_contraction_of_smallContrast
    [NeZero d]
    {W : Set (Vec d)} (hW : IsOpen W) {s : Vec d → ℝ}
    (hs : ContinuousOn s W) {u : H1Function W}
    (hu : IsWeaklyHarmonicOn s W u)
    {x : Vec d} {rho : ℝ} (hrho : 0 < rho)
    (hball : euclideanBall x rho ⊆ W)
    (kappa delta alpha : ℝ)
    (hd : 2 ≤ d) (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ smallContrastThreshold d alpha)
    (hdelta1 : delta < 1)
    (hclose : ∀ y ∈ euclideanBall x rho,
      |kappa⁻¹ * s y - 1| ≤ delta)
    (n : ℕ) :
    let uBall := u.restrict (isOpen_euclideanBall x rho) hball
    let K := smallContrastSchauderConstant d *
      smallContrastDataSize d alpha (ballToUnitH1 x hrho uBall) (fun _ ↦ 0)
    let r := rho / (2 * (d : ℝ)) *
      (3 : ℝ) ^ (-((n + 1 : ℕ) : ℝ))
    oscillationOn (Metric.ball x r)
        (euclideanBallAverageRepresentative u.toFun) ≤
      K * rho * (3 : ℝ) ^ (-alpha * (n : ℝ)) := by
  let uBall := u.restrict (isOpen_euclideanBall x rho) hball
  let K := smallContrastSchauderConstant d *
    smallContrastDataSize d alpha (ballToUnitH1 x hrho uBall) (fun _ ↦ 0)
  let r := rho / (2 * (d : ℝ)) *
    (3 : ℝ) ^ (-((n + 1 : ℕ) : ℝ))
  change oscillationOn (Metric.ball x r)
      (euclideanBallAverageRepresentative u.toFun) ≤
    K * rho * (3 : ℝ) ^ (-alpha * (n : ℝ))
  have hd0 : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hpowPos : 0 < (3 : ℝ) ^ (-((n + 1 : ℕ) : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hr : 0 < r := by
    dsimp only [r]
    exact mul_pos (div_pos hrho (mul_pos (by norm_num) hd0)) hpowPos
  have hpowLt : (3 : ℝ) ^ (-((n + 1 : ℕ) : ℝ)) < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    exact neg_lt_zero.mpr (by positivity)
  have hrInner : (d : ℝ) * r < rho / 2 := by
    dsimp only [r]
    field_simp [hd0.ne']
    nlinarith
  obtain ⟨g, _hcontG, _haeG, hholderG, hcanonical⟩ :=
    exists_physicalBallRepresentative_smallContrast hW hs hu hrho hball
      kappa delta alpha hd halpha hdelta0 hdelta hdelta1 hclose
  have hmetricSub : Metric.ball x r ⊆ euclideanBall x (rho / 2) :=
    (metricBall_subset_euclideanBall_dimension x r).trans
      (euclideanBall_subset_euclideanBall
        (mul_nonneg (Nat.cast_nonneg d) hr.le) hrInner)
  have hcongr : oscillationOn (Metric.ball x r)
      (euclideanBallAverageRepresentative u.toFun) =
        oscillationOn (Metric.ball x r) g :=
    oscillationOn_congr_of_eqOn fun y hy ↦ hcanonical y (hmetricSub hy)
  rw [hcongr]
  have hK : 0 ≤ K := by
    exact mul_nonneg (smallContrastSchauderConstant_nonneg d)
      (smallContrastDataSize_nonneg halpha.2 _ _)
  have halpha0 : 0 ≤ alpha := by linarith [halpha.1]
  have hraw := oscillationOn_metricBall_le_of_euclideanHolder
    hr hrInner halpha0
    (mul_nonneg hK (Real.rpow_nonneg hrho.le _)) hholderG
  have htwoDr : 2 * (d : ℝ) * r =
      rho * (3 : ℝ) ^ (-((n + 1 : ℕ) : ℝ)) := by
    dsimp only [r]
    field_simp [hd0.ne']
  rw [htwoDr] at hraw
  have hfactor :
      rho ^ (1 - alpha) *
          (rho * (3 : ℝ) ^ (-((n + 1 : ℕ) : ℝ))) ^ alpha =
        rho * (3 : ℝ) ^ (-alpha * ((n + 1 : ℕ) : ℝ)) := by
    rw [Real.mul_rpow hrho.le (Real.rpow_nonneg (by norm_num) _),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      show -((n + 1 : ℕ) : ℝ) * alpha =
        -alpha * ((n + 1 : ℕ) : ℝ) by ring,
      ← mul_assoc, ← Real.rpow_add hrho]
    rw [show 1 - alpha + alpha = (1 : ℝ) by ring, Real.rpow_one]
  have htriadic : (3 : ℝ) ^ (-alpha * ((n + 1 : ℕ) : ℝ)) ≤
      (3 : ℝ) ^ (-alpha * (n : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    norm_num
    nlinarith
  calc
    oscillationOn (Metric.ball x r) g ≤
        K * rho ^ (1 - alpha) *
          (rho * (3 : ℝ) ^ (-((n + 1 : ℕ) : ℝ))) ^ alpha := hraw
    _ = K * (rho ^ (1 - alpha) *
          (rho * (3 : ℝ) ^ (-((n + 1 : ℕ) : ℝ))) ^ alpha) := by ring
    _ = K * (rho * (3 : ℝ) ^
          (-alpha * ((n + 1 : ℕ) : ℝ))) := by rw [hfactor]
    _ ≤ K * (rho * (3 : ℝ) ^ (-alpha * (n : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left htriadic hrho.le) hK
    _ = K * rho * (3 : ℝ) ^ (-alpha * (n : ℝ)) := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
