module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.OffGridWindows
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SubunitGeometry

@[expose] public section

/-!
# Theta ladder: off-grid triadic windows

The stopped recurrence is indexed by grid shifts relative to the parent
centre, whereas the Campanato telescope is centred at an arbitrary physical
point.  This file supplies the relative grid centre and the two inclusions
used in the readout.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

noncomputable section

variable {d : ℕ}

private theorem mem_cube_of_norm_le_quarter {m : ℕ} {x : Vec d}
    (hx : ‖x‖ ≤ (3 : ℝ) ^ m / 4) :
    x ∈ cube d (m : ℤ) := by
  rw [cube, mem_openCubeSet_originCube_iff]
  intro i
  have hi : |x i| ≤ ‖x‖ := by
    have hcoord :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mp le_rfl i
    simpa only [Real.norm_eq_abs] using hcoord
  have hpow : 0 < (3 : ℝ) ^ m := by positivity
  rw [zpow_natCast]
  constructor
  · have habs := abs_le.mp (hi.trans hx)
    nlinarith
  · have habs := abs_le.mp (hi.trans hx)
    nlinarith

private theorem norm_sub_le_of_coordinate_halfScale
    {n : ℕ} {x q : Vec d}
    (hcoord : ∀ i : Fin d,
      |x i - q i| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ n) :
    ‖x - q‖ ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
  refine (pi_norm_le_iff_of_nonneg
    (by positivity : 0 ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ n)).2 ?_
  intro i
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using hcoord i

/-- A point in the middle quarter of a scale-`m` parent admits, at every
scale `s ≤ m-3`, a relative grid centre.  Its scale-`s` off-grid cube lies in
the next grid cube, while the scale-`m-2` cube at that same grid centre lies
inside the closed middle-three-quarters collar used by the consumer. -/
theorem exists_relativeGridCentre_with_campanatoWindows
    {m s : ℕ} (hsm : s + 3 ≤ m) {z x : Vec d}
    (hx : ‖x - z‖ ≤ (3 : ℝ) ^ m / 4) :
    ∃ q : Vec d,
      OnTriadicGrid s q ∧ q ∈ cube d (m : ℤ) ∧
      translatedCube d (s : ℤ) x ⊆
        translatedCube d ((s : ℤ) + 1) (z + q) ∧
      translatedCube d ((m : ℤ) - 2) (z + q) ⊆
        {y : Vec d | ‖y - z‖ ≤ 3 * (3 : ℝ) ^ (m : ℤ) / 8} := by
  have hxrel : x - z ∈ cube d (m : ℤ) :=
    mem_cube_of_norm_le_quarter (by simpa only [norm_sub_rev] using hx)
  have hsm' : s ≤ m := by omega
  obtain ⟨q, hqgrid, hqmem, hcoord⟩ :=
    exists_holderGridCentre hxrel hsm'
  refine ⟨q, hqgrid, hqmem, ?_, ?_⟩
  · rw [translatedCube_eq_metricBall, translatedCube_eq_metricBall]
    apply Metric.ball_subset_ball'
    rw [dist_eq_norm]
    have hdist : ‖x - (z + q)‖ ≤
        (1 / 2 : ℝ) * (3 : ℝ) ^ s := by
      have hrel := norm_sub_le_of_coordinate_halfScale hcoord
      have hid : x - (z + q) = (x - z) - q := by abel
      rw [hid]
      exact hrel
    have hpow : (3 : ℝ) ^ ((s : ℤ) + 1) = 3 * (3 : ℝ) ^ s := by
      rw [zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
      rw [zpow_natCast]
      ring
    have hscale : 0 < (3 : ℝ) ^ s := by positivity
    rw [zpow_natCast, hpow]
    nlinarith [hdist]
  · intro y hy
    rw [translatedCube_eq_metricBall, Metric.mem_ball, dist_eq_norm] at hy
    have hqdist : ‖q‖ ≤
        (3 : ℝ) ^ m / 4 + (1 / 2 : ℝ) * (3 : ℝ) ^ s := by
      have hrel := norm_sub_le_of_coordinate_halfScale hcoord
      have htri := norm_add_le (x - z) (-(x - z - q))
      have hid : (x - z) + -(x - z - q) = q := by abel
      rw [hid, norm_neg] at htri
      exact htri.trans (add_le_add (by simpa only [norm_sub_rev] using hx) hrel)
    have hyz : ‖y - z‖ ≤ ‖y - (z + q)‖ + ‖q‖ := by
      have htri := norm_add_le (y - (z + q)) q
      have hid : y - (z + q) + q = y - z := by abel
      rwa [hid] at htri
    have hpowS : (3 : ℝ) ^ s ≤ (3 : ℝ) ^ (m - 3) := by
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hm3 : (3 : ℝ) ^ (m - 3) = (3 : ℝ) ^ m / 27 := by
      have hmge : 3 ≤ m := by omega
      rw [← pow_sub_mul_pow (a := (3 : ℝ)) hmge]
      norm_num
    have hpowTop : (3 : ℝ) ^ ((m : ℤ) - 2) = (3 : ℝ) ^ m / 9 := by
      rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
      norm_num
    rw [hpowTop] at hy
    have hpowPos : 0 < (3 : ℝ) ^ m := by positivity
    change ‖y - z‖ ≤ 3 * (3 : ℝ) ^ (m : ℤ) / 8
    rw [zpow_natCast]
    have hsbound : (1 / 2 : ℝ) * (3 : ℝ) ^ s ≤
        (3 : ℝ) ^ m / 54 := by
      calc
        (1 / 2 : ℝ) * (3 : ℝ) ^ s ≤
            (1 / 2 : ℝ) * (3 : ℝ) ^ (m - 3) := by gcongr
        _ = (3 : ℝ) ^ m / 54 := by rw [hm3]; ring
    calc
      ‖y - z‖ ≤ ‖y - (z + q)‖ + ‖q‖ := hyz
      _ ≤ (1 / 2 : ℝ) * ((3 : ℝ) ^ m / 9) +
          ((3 : ℝ) ^ m / 4 + (3 : ℝ) ^ m / 54) := by
        exact add_le_add hy.le
          (hqdist.trans (add_le_add_right hsbound _))
      _ ≤ 3 * (3 : ℝ) ^ m / 8 := by nlinarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
