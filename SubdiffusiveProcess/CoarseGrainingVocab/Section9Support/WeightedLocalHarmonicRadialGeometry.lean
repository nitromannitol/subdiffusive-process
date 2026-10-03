module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeGeometry
@[expose] public section

/-! Growing triadic witness squares and a compactly contained inner square. -/

set_option autoImplicit false
open Homogenization hiding cubeSet
open MeasureTheory Set
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonicRadial

private lemma mem_cubeSet_iff {d : ℕ} (Q : Cube d) (x : Vec d) :
    x ∈ cubeSet Q ↔ ∀ i, Q.1 i - Q.2 / 2 < x i ∧ x i < Q.1 i - Q.2 / 2 + Q.2 := by
  simp only [SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet, centeredAxisCube,
    axisCube, Set.mem_pi, Set.mem_univ, Set.mem_Ioo, forall_true_left]

def radialOuter (R : ℝ) : Cube 2 := (![1 + R / 2, 10 * R ^ 2], R)
def radialInner (R : ℝ) : Cube 2 := (![2 + R / 6, 10 * R ^ 2], R / 3)
def radialPoint (R : ℝ) : Vec 2 := ![3, 10 * R ^ 2]

theorem mem_radialOuter {R : ℝ} {x : Vec 2} : x ∈ cubeSet (radialOuter R) ↔
    (1 < x 0 ∧ x 0 < 1 + R) ∧
      (10 * R ^ 2 - R / 2 < x 1 ∧ x 1 < 10 * R ^ 2 + R / 2) := by
  rw [mem_cubeSet_iff]
  simp only [radialOuter, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem mem_radialInner {R : ℝ} {x : Vec 2} : x ∈ cubeSet (radialInner R) ↔
    (2 < x 0 ∧ x 0 < 2 + R / 3) ∧
      (10 * R ^ 2 - R / 6 < x 1 ∧ x 1 < 10 * R ^ 2 + R / 6) := by
  rw [mem_cubeSet_iff]
  simp only [radialInner, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem compactlyInside_radialInner {R : ℝ} (hR : 3 < R) :
    CompactlyInside (radialInner R) (radialOuter R) := by
  have h1 : cubeSet (radialInner R) ⊆
      ({x : Vec 2 | 2 ≤ x 0} ∩ {x : Vec 2 | x 0 ≤ 2 + R / 3}) ∩
        ({x : Vec 2 | 10 * R ^ 2 - R / 6 ≤ x 1} ∩
          {x : Vec 2 | x 1 ≤ 10 * R ^ 2 + R / 6}) := by
    intro x hx
    rw [mem_radialInner] at hx
    obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := hx
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hclosed : IsClosed
      (({x : Vec 2 | 2 ≤ x 0} ∩ {x : Vec 2 | x 0 ≤ 2 + R / 3}) ∩
        ({x : Vec 2 | 10 * R ^ 2 - R / 6 ≤ x 1} ∩
          {x : Vec 2 | x 1 ≤ 10 * R ^ 2 + R / 6})) :=
    ((isClosed_le continuous_const (continuous_apply (0 : Fin 2))).inter
      (isClosed_le (continuous_apply (0 : Fin 2)) continuous_const)).inter
      ((isClosed_le continuous_const (continuous_apply (1 : Fin 2))).inter
        (isClosed_le (continuous_apply (1 : Fin 2)) continuous_const))
  have h2 :
      (({x : Vec 2 | 2 ≤ x 0} ∩ {x : Vec 2 | x 0 ≤ 2 + R / 3}) ∩
        ({x : Vec 2 | 10 * R ^ 2 - R / 6 ≤ x 1} ∩
          {x : Vec 2 | x 1 ≤ 10 * R ^ 2 + R / 6})) ⊆ cubeSet (radialOuter R) := by
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hx
    obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := hx
    rw [mem_radialOuter]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  show closure (cubeSet (radialInner R)) ⊆ cubeSet (radialOuter R)
  calc closure (cubeSet (radialInner R))
      ⊆ closure (({x : Vec 2 | 2 ≤ x 0} ∩ {x : Vec 2 | x 0 ≤ 2 + R / 3}) ∩
          ({x : Vec 2 | 10 * R ^ 2 - R / 6 ≤ x 1} ∩
            {x : Vec 2 | x 1 ≤ 10 * R ^ 2 + R / 6})) := closure_mono h1
    _ = ({x : Vec 2 | 2 ≤ x 0} ∩ {x : Vec 2 | x 0 ≤ 2 + R / 3}) ∩
        ({x : Vec 2 | 10 * R ^ 2 - R / 6 ≤ x 1} ∩
          {x : Vec 2 | x 1 ≤ 10 * R ^ 2 + R / 6}) := IsClosed.closure_eq hclosed
    _ ⊆ cubeSet (radialOuter R) := h2

theorem radialPoint_mem_radialInner {R : ℝ} (hR : 3 < R) :
    radialPoint R ∈ cubeSet (radialInner R) := by
  rw [mem_radialInner]
  simp only [radialPoint, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem volume_radialOuter {R : ℝ} (hR : 0 ≤ R) :
    (volume (cubeSet (radialOuter R))).toReal = R ^ 2 := by
  have h : cubeSet (radialOuter R) = centeredAxisCube (![1 + R / 2, 10 * R ^ 2]) R := by
    rfl
  rw [h]
  exact SubdiffusiveProcess.Section9.volume_centeredAxisCube_toReal (![1 + R / 2, 10 * R ^ 2]) hR

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonicRadial
