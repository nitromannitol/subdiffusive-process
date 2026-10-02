import SubdiffusiveProcess.LambdaStability.FieldAdapters

/-! Passing from the paper's open-cube inclusion to the internal partition cubes. -/
open Homogenization

noncomputable section
namespace SubdiffusiveProcess.LambdaStability
variable {d : ℕ}

theorem origin_translate_coordinates {x : Vec d}
    (hx : translateSet x (openCubeSet (originCube d (-1))) ⊆ openCubeSet (originCube d 0)) :
    ∀ i, -(1 / 3 : ℝ) ≤ x i ∧ x i ≤ 1 / 3 := by
  classical
  have hzero : (0 : Vec d) ∈ openCubeSet (originCube d (-1)) := by
    rw [mem_openCubeSet_originCube_iff]
    intro i
    norm_num
  have hxroot : x ∈ openCubeSet (originCube d 0) := hx
    (mem_translateSet_iff_sub_mem.2 (by simpa only [sub_self] using hzero))
  have hbase := mem_openCubeSet_originCube_iff.1 hxroot
  norm_num only [zpow_zero, mul_one] at hbase
  have htest : ∀ (i : Fin d) (z : ℝ), -(1 / 6 : ℝ) < z → z < 1 / 6 →
      -(1 / 2 : ℝ) < x i + z ∧ x i + z < 1 / 2 := by
    intro i z hz0 hz1
    let v : Vec d := fun j => if j = i then z else 0
    have hv : v ∈ openCubeSet (originCube d (-1)) := by
      rw [mem_openCubeSet_originCube_iff]
      intro j
      dsimp [v]
      split_ifs
      · norm_num
        exact ⟨hz0, hz1⟩
      · norm_num
    have hout := hx (mem_translateSet_iff_sub_mem.2
      (by simpa only [add_sub_cancel_left] using hv) : x + v ∈ translateSet x _)
    have hi := mem_openCubeSet_originCube_iff.1 hout i
    simpa only [zpow_zero, mul_one, Pi.add_apply, v, if_pos rfl] using hi
  intro i
  constructor
  · by_contra h
    have hlt : x i < -(1 / 3 : ℝ) := lt_of_not_ge h
    have hz := htest i (-1 / 3 - x i / 2) (by linarith) (by linarith [hbase i])
    linarith
  · by_contra h
    have hlt : (1 / 3 : ℝ) < x i := lt_of_not_ge h
    have hz := htest i (1 / 3 - x i / 2) (by linarith [hbase i]) (by linarith)
    linarith

theorem origin_halfOpen_containment {x : Vec d}
    (hx : translateSet x (openCubeSet (originCube d (-1))) ⊆ openCubeSet (originCube d 0)) :
    translateSet x (cubeSet (originCube d (-1))) ⊆ cubeSet (originCube d 0) := by
  have hb := origin_translate_coordinates hx
  intro y hy
  have hy' := mem_cubeSet_originCube_iff.1 (mem_translateSet_iff_sub_mem.1 hy)
  rw [mem_cubeSet_originCube_iff]
  intro i
  have hcell := hy' i
  norm_num only [zpow_neg_one, zpow_zero, mul_one] at hcell ⊢
  change -(1 / 2 : ℝ) ≤ y i ∧ y i < 1 / 2
  change -(1 / 6 : ℝ) ≤ y i - x i ∧ y i - x i < 1 / 6 at hcell
  constructor <;> linarith [hb i]

end SubdiffusiveProcess.LambdaStability
