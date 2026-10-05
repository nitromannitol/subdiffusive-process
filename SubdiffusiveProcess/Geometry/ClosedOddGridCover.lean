module

public import SubdiffusiveProcess.Analysis.GlobalTriadicAverages
public import Mathlib.Topology.Baire.LocallyCompactRegular

@[expose] public section

open MeasureTheory Set TopologicalSpace
noncomputable section
namespace SubdiffusiveProcess

theorem oddGridCell_closure_iUnion_eq_closure_centeredCube
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (m : ℕ) :
    (⋃ k : OddGridIndex d m,
      closure (oddGridCell z r hr m k : Set (SpatialCoordinates d))) =
      closure (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  let U : Set (SpatialCoordinates d) := ⋃ k : OddGridIndex d m,
    (oddGridCell z r hr m k : Set (SpatialCoordinates d))
  let B : Set (SpatialCoordinates d) :=
    ⋃ i : Fin d, ⋃ q : Fin (2 * m + 2), triadicFaceSet z r m i q
  have hBdense : Dense Bᶜ := by
    let F : (Fin d × Fin (2 * m + 2)) → Set (SpatialCoordinates d) :=
      fun p => triadicFaceSet z r m p.1 p.2
    have hopen : ∀ p, IsOpen (F p)ᶜ := by
      intro p
      apply isOpen_compl_iff.mpr
      change IsClosed ((fun x : SpatialCoordinates d => x p.1) ⁻¹' {z p.1 - r / 2 +
        (p.2 : ℝ) * (r / (2 * (m : ℝ) + 1))})
      exact isClosed_singleton.preimage (continuous_apply p.1)
    have hdense : ∀ p, Dense (F p)ᶜ := by
      intro p
      apply Dense.preimage (dense_compl_singleton _)
      exact isOpenMap_eval p.1
    have h := dense_iInter_of_isOpen hopen hdense
    rw [show Bᶜ = ⋂ p, (F p)ᶜ by
      ext x
      simp only [B, F, compl_iUnion, mem_iInter, mem_compl_iff]
      constructor
      · intro h p
        exact h p.1 p.2
      · intro h i q
        exact h (i, q)]
    exact h
  have hcubeU : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ closure U := by
    intro x hx
    rw [mem_closure_iff]
    intro V hV hxV
    have hVcube : IsOpen (V ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      hV.inter (centeredCube z r hr).isOpen
    have hne : (V ∩ (centeredCube z r hr : Set (SpatialCoordinates d)) ∩ Bᶜ).Nonempty := by
      exact hBdense.inter_open_nonempty _ hVcube ⟨x, hxV, hx⟩
    obtain ⟨y, hy⟩ := hne
    have hyV : y ∈ V := hy.1.1
    have hycube : y ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) := hy.1.2
    have hyB : y ∈ Bᶜ := hy.2
    obtain ⟨k, hyk⟩ := mem_triadicCell_of_mem_cube_of_not_face z hr m y hycube (by
      intro i q hq
      exact hyB (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨q, hq⟩⟩))
    have hyU : y ∈ U := by
      dsimp [U]
      exact mem_iUnion.mpr ⟨k, hyk⟩
    exact ⟨y, hyV, hyU⟩
  have hclosureU : closure U = closure (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    apply Subset.antisymm
    · apply closure_mono
      intro x hx
      rcases mem_iUnion.1 hx with ⟨k, hxk⟩
      exact oddGridCell_subset z hr m k hxk
    · exact closure_minimal hcubeU isClosed_closure
  have hlocal : LocallyFinite (fun k : OddGridIndex d m =>
      (oddGridCell z r hr m k : Set (SpatialCoordinates d))) := by
    exact locallyFinite_of_finite _
  calc
    _ = closure (⋃ k : OddGridIndex d m,
        (oddGridCell z r hr m k : Set (SpatialCoordinates d))) :=
      (LocallyFinite.closure_iUnion (f := fun k : OddGridIndex d m =>
        (oddGridCell z r hr m k : Set (SpatialCoordinates d))) hlocal).symm
    _ = closure U := rfl
    _ = closure (centeredCube z r hr : Set (SpatialCoordinates d)) := hclosureU

end SubdiffusiveProcess
