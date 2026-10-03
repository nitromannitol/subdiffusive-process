module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeAuxGeometry

@[expose] public section

/-!
# Uniform auxiliary covers for the fixed original family

A finite family of compact interiors admits one outer depth and one cardinality
bound, after any prescribed inner depth. These choices precede the model and
native scale. The accompanying actual Lebesgue-volume ratio has a positive
lower bound unchanged by translations and dilations.
-/

set_option autoImplicit false
open Set MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.Section9 (centeredAxisCube)
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- One common outer depth and cardinality bound suffice for a finite family of compact interiors. -/
theorem exists_goodCube_auxiliary_covers {d : ℕ} {ι : Type*} [Finite ι]
    (K W : ι → Set (Vec d)) (hK : ∀ i, IsCompact (K i))
    (hW : ∀ i, IsOpen (W i)) (hKW : ∀ i, K i ⊆ W i)
    (eta : ι → ℝ) (heta : ∀ i, 0 < eta i) (j k0 : ℕ) :
    ∃ (k N : ℕ) (centers : ι → Finset (Vec d)), k0 ≤ k ∧
      ∀ i, (3 : ℝ) ^ (-(k : ℤ)) ≤ eta i ∧
        (centers i).card ≤ N ∧
        (↑(centers i) : Set (Vec d)) ⊆ K i ∧
        K i ⊆ ⋃ x ∈ centers i,
          centeredAxisCube x ((3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ (-(k : ℤ))) ∧
        ∀ x ∈ centers i,
          closure (centeredAxisCube x ((3 : ℝ) ^ (-(k : ℤ)))) ⊆ W i := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  choose J hJ using fun i =>
    exists_goodCube_auxiliary_depth (hK i) (hW i) (hKW i) (heta i)
  set k := max k0 (Finset.univ.sup (fun i => J i)) with hk
  have hJk : ∀ i, J i ≤ k := fun i =>
    le_trans (Finset.le_sup (s := (Finset.univ : Finset ι)) (f := J)
      (Finset.mem_univ i)) (le_max_right _ _)
  have hpos : 0 < ((3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ (-(k : ℤ))) :=
    mul_pos (zpow_pos (by norm_num : (0 : ℝ) < 3) (-(j : ℤ)))
      (zpow_pos (by norm_num : (0 : ℝ) < 3) (-(k : ℤ)))
  choose centers hc1 hc2 using fun i =>
    exists_goodCube_finite_center_cover (hK i) hpos
  refine ⟨k, Finset.univ.sup (fun i => (centers i).card), centers,
    le_max_left _ _, ?_⟩
  intro i
  refine ⟨(hJ i k (hJk i)).1, Finset.le_sup (s := (Finset.univ : Finset ι))
    (f := fun i : ι => (centers i).card) (Finset.mem_univ i), hc1 i, hc2 i, ?_⟩
  intro x hx
  exact (hJ i k (hJk i)).2 x (hc1 i hx)

/-- The inner-to-parent volume ratio has a positive reference lower bound at every positive dilation. -/
theorem goodCube_auxiliary_volume_ratio {d : ℕ}
    (x y : Vec d) (j k : ℕ) {s L : ℝ}
    (hs : 0 < s) (hL : 0 < L) (hL1 : L ≤ 1) :
    0 < ((3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ (-(k : ℤ))) ^ d ∧
      (volume (centeredAxisCube x
        (s * ((3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ (-(k : ℤ)))))).toReal /
          (volume (centeredAxisCube y (s * L))).toReal =
        ((3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ (-(k : ℤ))) ^ d / L ^ d ∧
      ((3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ (-(k : ℤ))) ^ d ≤
        (volume (centeredAxisCube x
          (s * ((3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ (-(k : ℤ)))))).toReal /
          (volume (centeredAxisCube y (s * L))).toReal := by
  set ρ := ((3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ (-(k : ℤ))) with hρ
  have h3j : (0 : ℝ) < (3 : ℝ) ^ (-(j : ℤ)) := zpow_pos (by norm_num) _
  have h3k : (0 : ℝ) < (3 : ℝ) ^ (-(k : ℤ)) := zpow_pos (by norm_num) _
  have hρpos : (0 : ℝ) < ρ := mul_pos h3j h3k
  have hratio : (volume (centeredAxisCube x (s * ρ))).toReal /
      (volume (centeredAxisCube y (s * L))).toReal = ρ ^ d / L ^ d := by
    rw [SubdiffusiveProcess.Section9.volume_centeredAxisCube_toReal x (by positivity),
      SubdiffusiveProcess.Section9.volume_centeredAxisCube_toReal y (mul_nonneg hs.le hL.le)]
    simp only [mul_pow]
    field_simp
  refine ⟨pow_pos hρpos d, hratio, ?_⟩
  rw [hratio, le_div_iff₀ (pow_pos hL d)]
  have hLpow : L ^ d ≤ 1 := pow_le_one₀ hL.le hL1
  have hρnn : (0 : ℝ) ≤ ρ ^ d := pow_nonneg hρpos.le d
  have := mul_le_mul_of_nonneg_right hLpow hρnn
  nlinarith

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
