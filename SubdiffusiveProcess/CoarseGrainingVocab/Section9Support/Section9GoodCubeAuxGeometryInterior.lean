module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeAuxGeometryFraction
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeReferenceGeometry

@[expose] public section

/-!
# A uniform compact-interior fraction for the torsion profile

Compact containment inside each original parent supplies an interior fraction.
Taking a finite common upper bound gives one `theta` strictly between zero and
one. It works for all selected compact sets before any model or native scale,
and is preserved by every positive affine dilation and translation.
-/

set_option autoImplicit false
open Set MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.Section9 (centeredAxisCube)
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- One strict interior fraction works for finitely many compact interiors and all their positive affine transports. -/
theorem exists_goodCube_uniform_interior_fraction {d : ℕ} {ι : Type*} [Finite ι]
    (K : ι → Set (Vec d)) (B : ι → Cube d)
    (hK : ∀ i, IsCompact (K i)) (hB : ∀ i, 0 < (B i).2)
    (hKB : ∀ i, K i ⊆ cubeSet (B i)) :
    ∃ theta : ℝ, 0 < theta ∧ theta < 1 ∧
      ∀ i, K i ⊆ centeredAxisCube (B i).1 (theta * (B i).2) ∧
        ∀ (y : Vec d) (s : ℝ), 0 < s →
          affinePhi y s '' K i ⊆
            centeredAxisCube (affinePhi y s (B i).1) (theta * (s * (B i).2)) := by
  classical
  have hstep : ∀ (i : ι), ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      K i ⊆ centeredAxisCube (B i).1 (a * (B i).2) := by
    intro (i : ι)
    obtain ⟨a, ha0, ha1, hsub⟩ :=
      exists_goodCube_compact_interior_fraction (d := d) (hK i) (B i) (hB i) (hKB i)
    exact ⟨a, ha0, ha1, hsub⟩
  choose a ha0 ha1 hsub using hstep
  obtain ⟨theta, hθ0, hθ1, hθle⟩ :=
    exists_goodCube_common_fraction (ι := ι) a ha1
  refine ⟨theta, hθ0, hθ1, ?_⟩
  intro (i : ι)
  have hle : a i * (B i).2 ≤ theta * (B i).2 :=
    mul_le_mul_of_nonneg_right (hθle i) (le_of_lt (hB i))
  have hbase : K i ⊆ centeredAxisCube (B i).1 (theta * (B i).2) :=
    (hsub i).trans (centeredAxisCube_mono hle)
  refine ⟨hbase, ?_⟩
  intro (y : Vec d) (s : ℝ) hs
  have hscale : s * (theta * (B i).2) = theta * (s * (B i).2) := by ring
  show (fun x => y + s • x) '' K i ⊆
    centeredAxisCube (y + s • (B i).1) (theta * (s * (B i).2))
  rw [← hscale, goodCube_affine_cube_image y (B i).1 (theta * (B i).2) hs]
  exact Set.image_mono hbase

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
