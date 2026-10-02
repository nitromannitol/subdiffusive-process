import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeAuxGeometry

/-!
# Auxiliary pairs for the good-cube torsion argument

The finite pairs used by the harmonic oscillation test have the same cardinality as their centers, positive inner side, and compact inclusion in the outer middle half at every integer scale.
-/

set_option autoImplicit false
open Set MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.Section9 (centeredAxisCube)
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Concentric auxiliary pairs at outer integer scale and relative inner depth. -/
def goodCubeAuxiliaryPairs {d : ℕ} (centers : Finset (Vec d))
    (j : ℕ) (m : ℤ) : Finset (Cube d × Cube d) := by
  classical
  exact centers.image (fun x =>
    ((x, (3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ m), (x, (3 : ℝ) ^ m)))

/-- The finite pairs used by the harmonic oscillation test have the same cardinality as their centers, positive inner side, and compact inclusion in the outer middle half at every integer scale. -/
theorem goodCube_auxiliary_pairs_geometry {d : ℕ}
    (centers : Finset (Vec d)) (j : ℕ) (m : ℤ) (hj : 1 ≤ j) :
    (goodCubeAuxiliaryPairs centers j m).card = centers.card ∧
      ∀ p ∈ goodCubeAuxiliaryPairs centers j m,
        0 < p.1.2 ∧ p.2.2 = (3 : ℝ) ^ m ∧
        p.1.2 = (3 : ℝ) ^ (-(j : ℤ)) * p.2.2 ∧
        closure (cubeSet p.1) ⊆ centeredAxisCube p.2.1 (p.2.2 / 2) := by
  classical
  have hinj : Function.Injective (fun x : Vec d =>
      ((x, (3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ m), (x, (3 : ℝ) ^ m))) := by
    intro a b h
    simp only [Prod.mk.injEq] at h
    exact h.1.1
  refine ⟨Finset.card_image_of_injective centers hinj, ?_⟩
  rintro p hp
  simp only [goodCubeAuxiliaryPairs, Finset.mem_image] at hp
  obtain ⟨x, hx, rfl⟩ := hp
  dsimp only
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have houter : 0 < (3 : ℝ) ^ m := zpow_pos h3pos m
  have hinner : 0 < (3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ m :=
    mul_pos (zpow_pos h3pos (-(j : ℤ))) houter
  have hle : (3 : ℝ) ^ (-(j : ℤ)) ≤ 1 / 3 := by
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    have hinv : (3 : ℝ)⁻¹ = 1 / 3 := by norm_num
    rw [hinv]
    have hp : (1 / 3 : ℝ) ^ j ≤ (1 / 3 : ℝ) ^ 1 :=
      pow_le_pow_of_le_one (a := (1 / 3 : ℝ)) (by norm_num) (by norm_num) hj
    simpa only [pow_one] using hp
  have hlt : (3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ m < (3 : ℝ) ^ m / 2 := by
    have h2 : (3 : ℝ) ^ m / 2 = (1 / 2 : ℝ) * (3 : ℝ) ^ m := by ring
    have step1 : (3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ m ≤ (1 / 3) * (3 : ℝ) ^ m :=
      mul_le_mul_of_nonneg_right hle (le_of_lt houter)
    have step2 : (1 / 3 : ℝ) * (3 : ℝ) ^ m < (1 / 2) * (3 : ℝ) ^ m :=
      mul_lt_mul_of_pos_right (by norm_num) houter
    rw [h2]
    linarith
  refine ⟨hinner, rfl, rfl, ?_⟩
  exact closure_centeredAxisCube_subset hlt

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
