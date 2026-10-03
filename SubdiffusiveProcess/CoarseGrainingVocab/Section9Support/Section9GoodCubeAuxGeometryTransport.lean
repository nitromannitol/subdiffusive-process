module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeAuxGeometry
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeReferenceGeometry

@[expose] public section

/-!
# Auxiliary transport for the good-cube torsion argument

Native translations and triadic dilations preserve the cover, all outer closure inclusions, and exact cardinality. Integer subtraction retains auxiliary cubes below scale one.
-/

set_option autoImplicit false
open Set MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.Section9 (centeredAxisCube)
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Centers transported by the native translation and dilation. -/
def goodCubeAuxiliaryCenters {d : ℕ} (centers : Finset (Vec d))
    (y : Vec d) (n : ℕ) : Finset (Vec d) := by
  classical
  exact centers.image (affinePhi y ((3 : ℝ) ^ n))

/-- Native translations and triadic dilations preserve the cover, all outer closure inclusions, and exact cardinality. Integer subtraction retains auxiliary cubes below scale one. -/
theorem goodCube_auxiliary_cover_transport {d : ℕ} {K W : Set (Vec d)}
    (centers : Finset (Vec d)) (j k : ℕ)
    (hcover : K ⊆ ⋃ x ∈ centers,
      centeredAxisCube x ((3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ (-(k : ℤ))))
    (hinside : ∀ x ∈ centers,
      closure (centeredAxisCube x ((3 : ℝ) ^ (-(k : ℤ)))) ⊆ W)
    (y : Vec d) (n : ℕ) :
    (goodCubeAuxiliaryCenters centers y n).card = centers.card ∧
      affinePhi y ((3 : ℝ) ^ n) '' K ⊆
        ⋃ x ∈ goodCubeAuxiliaryCenters centers y n,
          centeredAxisCube x ((3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ ((n : ℤ) - k)) ∧
      ∀ x ∈ goodCubeAuxiliaryCenters centers y n,
        closure (centeredAxisCube x ((3 : ℝ) ^ ((n : ℤ) - k))) ⊆
          affinePhi y ((3 : ℝ) ^ n) '' W := by
  classical
  let s : ℝ := (3 : ℝ) ^ n
  have hs : 0 < s := pow_pos (by norm_num) n
  have hscale : s * (3 : ℝ) ^ (-(k : ℤ)) = (3 : ℝ) ^ ((n : ℤ) - k) := by
    dsimp only [s]
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
  have hinner : s * ((3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ (-(k : ℤ))) =
      (3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ ((n : ℤ) - k) := by
    rw [← hscale]
    ring
  refine ⟨?_, ?_, ?_⟩
  · change (centers.image (affinePhi y s)).card = centers.card
    exact Finset.card_image_of_injective centers (affinePhi_injective y hs.ne')
  · rintro z ⟨w, hw, rfl⟩
    obtain ⟨x, hx, hwx⟩ := Set.mem_iUnion₂.mp (hcover hw)
    refine Set.mem_iUnion₂.mpr ⟨affinePhi y s x, ?_, ?_⟩
    · change affinePhi y s x ∈ centers.image (affinePhi y s)
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    · rw [← hinner]
      exact (goodCube_mem_affine_cube y w x _ hs).mpr hwx
  · intro x hx
    change x ∈ centers.image (affinePhi y s) at hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    change closure (centeredAxisCube (y + s • a) ((3 : ℝ) ^ ((n : ℤ) - k))) ⊆
      affinePhi y s '' W
    rw [← hscale, goodCube_affine_cube_image y a _ hs]
    change closure (affinePhi y s '' centeredAxisCube a ((3 : ℝ) ^ (-(k : ℤ)))) ⊆
      affinePhi y s '' W
    rw [closure_image_affinePhi y hs.ne']
    exact Set.image_mono (hinside a ha)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
