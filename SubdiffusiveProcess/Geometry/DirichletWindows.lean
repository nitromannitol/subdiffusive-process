module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.LiouvilleGeometry
public import SubdiffusiveProcess.Lane4.HolderSobolevBridge

@[expose] public section

/-! Native truncated cubes become physical ball-cube intersections under dilation.
The identities apply to every center and do not supply any solution estimate. -/
open Set Metric SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay SubdiffusiveProcess.Lane4
open scoped Pointwise
namespace SubdiffusiveProcess

/-- Translation carries a ball to the ball with translated center. -/
theorem translateSet_ball {d : ℕ} (z c : Vec d) (r : ℝ) :
    translateSet z (ball c r) = ball (c+z) r := by
  ext x
  rw [mem_translateSet_iff_sub_mem,mem_ball,mem_ball]
  have hd : dist (x-z) c = dist x (c+z) := by
    rw [dist_eq_norm,dist_eq_norm]
    congr 1
    abel
  rw [hd]

/-- A translated native cube is a ball for the coordinate supremum metric. -/
theorem translatedCube_eq_sup_ball {d : ℕ} (j : ℤ) (x : Vec d) :
    translatedCube d j x = ball x ((3:ℝ)^j/2) := by
  ext y
  rw [mem_translatedCube_iff,Section6TheoremC.cube_eq_ball,mem_ball,mem_ball]
  rw [dist_zero_right,dist_eq_norm]
  congr 1
  ring

/-- The cutoff dilation identifies a truncated cube with its physical ball window. -/
theorem cutoff_truncatedCube_affine {d : ℕ} (N : ℕ) (j : ℤ) (w z : Vec d) :
    translateSet z (((3:ℝ)^N)⁻¹ • truncatedCube d N j ((3:ℝ)^N • (w-z))) =
      ball w ((((3:ℝ)^N)⁻¹*(3:ℝ)^j)/2) ∩
        (centeredCube z 1 zero_lt_one : Set (Vec d)) := by
  have hs : (0:ℝ) < (3:ℝ)^N := by positivity
  rw [truncatedCube,Set.smul_set_inter₀ (inv_ne_zero hs.ne'),translateSet_inter,
    translatedCube_eq_sup_ball,Section6TheoremC.cube_eq_ball,
    _root_.smul_ball (inv_ne_zero hs.ne'),_root_.smul_ball (inv_ne_zero hs.ne'),
    Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs),smul_smul,inv_mul_cancel₀ hs.ne',one_smul,
    smul_zero,translateSet_ball,translateSet_ball,sub_add_cancel,zero_add,zpow_natCast]
  change _ = _ ∩ Metric.ball z (1/2)
  congr 2 <;> field_simp <;> ring

/-- A physical point in the unit-side cube gives a native point in the origin cube. -/
theorem cutoff_nativeCentre_mem_cube {d : ℕ} (N : ℕ) (w z : Vec d)
    (hw : w ∈ (centeredCube z 1 zero_lt_one : Set (Vec d))) :
    (3:ℝ)^N • (w-z) ∈ cube d N := by
  have hs : (0:ℝ) < (3:ℝ)^N := by positivity
  rw [Section6TheoremC.cube_eq_ball,mem_ball,dist_zero_right,norm_smul,
    Real.norm_eq_abs,abs_of_pos hs,zpow_natCast]
  change dist w z < 1/2 at hw
  rw [dist_eq_norm] at hw
  have hh := mul_lt_mul_of_pos_left hw hs
  nlinarith only [hh]

/-- The native origin cube maps into the physical unit-side cube. -/
theorem cutoff_affine_mem_cube {d : ℕ} (N : ℕ) (z y : Vec d) (hy : y ∈ cube d N) :
    ((3:ℝ)^N)⁻¹ • y+z ∈ (centeredCube z 1 zero_lt_one : Set (Vec d)) := by
  have hs : (0:ℝ) < (3:ℝ)^N := by positivity
  rw [Section6TheoremC.cube_eq_ball,mem_ball,dist_zero_right,zpow_natCast] at hy
  change dist (((3:ℝ)^N)⁻¹ • y+z) z < 1/2
  rw [dist_eq_norm,add_sub_cancel_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs)]
  have hh := mul_lt_mul_of_pos_left hy (inv_pos.mpr hs)
  have hid : ((3:ℝ)^N)⁻¹*((1/2:ℝ)*(3:ℝ)^N)=1/2 := by field_simp
  rwa [hid] at hh

end SubdiffusiveProcess
