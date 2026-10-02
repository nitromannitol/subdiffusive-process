import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeAuxGeometryComplete
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeAuxGeometryPairs
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeAuxGeometryTransport




set_option autoImplicit false
open Set MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.Section9 (centeredAxisCube)
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The finite union of the center lists of every auxiliary target. -/
def goodCubeAuxiliaryCenterUnion {d : ℕ} {ι : Type*} [Finite ι]
    (centers : ι → Finset (Vec d)) : Finset (Vec d) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  exact Finset.univ.biUnion centers

/-- Membership in the finite union is witnessed by an actual auxiliary target index. -/
theorem mem_goodCube_auxiliary_center_union {d : ℕ} {ι : Type*} [Finite ι]
    (centers : ι → Finset (Vec d)) (x : Vec d) :
    x ∈ goodCubeAuxiliaryCenterUnion centers ↔ ∃ i, x ∈ centers i := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  simp only [goodCubeAuxiliaryCenterUnion, Finset.mem_biUnion, Finset.mem_univ, true_and]

/-- Each auxiliary center contributes the pair with its normalized inner depth. -/
theorem goodCube_auxiliary_pair_catalog_mem {d : ℕ} {ι : Type*} [Finite ι]
    (centers : ι → Finset (Vec d)) (j k : ℕ) (i : ι) (x : Vec d)
    (hx : x ∈ centers i) :
    ((x, (3 : ℝ) ^ (-((j + k : ℕ) : ℤ))), (x, (3 : ℝ) ^ (-(k : ℤ)))) ∈
      goodCubeAuxiliaryPairs (goodCubeAuxiliaryCenterUnion centers) j (-(k : ℤ)) := by
  classical
  rw [← goodCube_auxiliary_inner_side_add j k]
  exact Finset.mem_image.mpr
    ⟨x, (mem_goodCube_auxiliary_center_union centers x).mpr ⟨i, hx⟩, rfl⟩

/-- The reference pair catalogue has exact depths, harmonic geometry, and all outer cubes inside the unit cube. -/
theorem goodCube_auxiliary_reference_pair_catalog {d : ℕ}
    (X : Finset (Vec d)) (j k : ℕ) (hj : 1 ≤ j)
    (hX : ∀ x ∈ X, cubeSet (x, (3 : ℝ) ^ (-(k : ℤ))) ⊆
      cubeSet ((0 : Vec d), (1 : ℝ))) :
    (goodCubeAuxiliaryPairs X j (-(k : ℤ))).card = X.card ∧
      ∀ p ∈ goodCubeAuxiliaryPairs X j (-(k : ℤ)),
        0 < p.1.2 ∧ p.2.2 = (3 : ℝ) ^ (-(k : ℤ)) ∧
        p.1.2 = (3 : ℝ) ^ (-((j + k : ℕ) : ℤ)) ∧
        p.1.2 = (3 : ℝ) ^ (-(j : ℤ)) * p.2.2 ∧
        closure (cubeSet p.1) ⊆ centeredAxisCube p.2.1 (p.2.2 / 2) ∧
        cubeSet p.2 ⊆ cubeSet ((0 : Vec d), (1 : ℝ)) := by
  classical
  obtain ⟨hcard, hgeo⟩ := goodCube_auxiliary_pairs_geometry X j (-(k : ℤ)) hj
  refine ⟨hcard, ?_⟩
  intro p hp
  obtain ⟨hpos, hout, hratio, hclo⟩ := hgeo p hp
  have hinner : p.1.2 = (3 : ℝ) ^ (-((j + k : ℕ) : ℤ)) := by
    rw [hratio, hout, goodCube_auxiliary_inner_side_add j k]
  have houtsub : cubeSet p.2 ⊆ cubeSet ((0 : Vec d), (1 : ℝ)) := by
    unfold goodCubeAuxiliaryPairs at hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    exact hX x hx
  exact ⟨hpos, hout, hinner, hratio, hclo, houtsub⟩

/-- Construct the finite depth-and-center catalogue containing all original, quarter, and auxiliary outer tests. -/
theorem exists_goodCube_cube_test_catalog {d : ℕ} {ι : Type*} [Finite ι]
    (Qfam : Set (Cube d)) (hfin : Qfam.Finite) (depth : Qfam → ℕ)
    (hdepth : ∀ Q : Qfam, Q.val.2 = (3 : ℝ) ^ (-(depth Q : ℤ)))
    (hinside : ∀ Q ∈ Qfam, cubeSet Q ⊆ cubeSet ((0 : Vec d), (1 : ℝ)))
    (centers : ι → Finset (Vec d)) (k : ℕ)
    (haux : ∀ i, ∀ x ∈ centers i,
      cubeSet (x, (3 : ℝ) ^ (-(k : ℤ))) ⊆ cubeSet ((0 : Vec d), (1 : ℝ))) :
    ∃ (G : Finset (ℕ × Vec d)) (J : ℕ), k ≤ J ∧
      (∀ q ∈ G, q.1 ≤ J ∧
        cubeSet (q.2, (3 : ℝ) ^ (-(q.1 : ℤ))) ⊆ cubeSet ((0 : Vec d), (1 : ℝ))) ∧
      (∀ Q : Qfam, (depth Q, Q.val.1) ∈ G) ∧
      (2, (0 : Vec d)) ∈ G ∧
      ∀ i, ∀ x ∈ centers i, (k, x) ∈ G := by
  classical
  letI : Finite Qfam := hfin.to_subtype
  letI : Fintype Qfam := Fintype.ofFinite Qfam
  set S : Finset (ℕ × Vec d) :=
    Finset.univ.image (fun Q : Qfam => (depth Q, Q.val.1)) with hS
  set A : Finset (ℕ × Vec d) :=
    (goodCubeAuxiliaryCenterUnion centers).image (fun x : Vec d => (k, x)) with hA
  refine ⟨insert (2, (0 : Vec d)) (S ∪ A),
    max k ((insert (2, (0 : Vec d)) (S ∪ A)).sup (fun q : ℕ × Vec d => q.1)),
    le_max_left _ _, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have hle : q.1 ≤ max k ((insert (2, (0 : Vec d)) (S ∪ A)).sup
        (fun q : ℕ × Vec d => q.1)) :=
      (Finset.le_sup (f := fun q : ℕ × Vec d => q.1) hq).trans (le_max_right _ _)
    refine ⟨hle, ?_⟩
    simp only [hS, hA, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hq
    rcases hq with rfl | hQ | hx
    · change centeredAxisCube (0 : Vec d) ((3 : ℝ) ^ (-(2 : ℤ))) ⊆
        centeredAxisCube (0 : Vec d) 1
      apply centeredAxisCube_mono
      norm_num
    · obtain ⟨Q, -, rfl⟩ := hQ
      simpa only [cubeSet, hdepth Q] using hinside Q.val Q.property
    · obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨i, hxi⟩ := (mem_goodCube_auxiliary_center_union centers x).mp hx
      exact haux i x hxi
  · intro Q
    apply Finset.mem_insert_of_mem
    apply Finset.mem_union_left
    rw [hS]
    exact Finset.mem_image.mpr ⟨Q, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_insert_self _ _
  · intro i x hx
    apply Finset.mem_insert_of_mem
    apply Finset.mem_union_right
    rw [hA]
    exact Finset.mem_image.mpr ⟨x, (mem_goodCube_auxiliary_center_union centers x).mpr ⟨i, hx⟩, rfl⟩

/-- Construct one actual cube catalogue and one actual auxiliary pair catalogue with common finite bounds. -/
theorem exists_goodCube_unified_test_catalog {d : ℕ} {ι : Type*} [Finite ι]
    (Qfam : Set (Cube d)) (hfin : Qfam.Finite) (depth : Qfam → ℕ)
    (hdepth : ∀ Q : Qfam, Q.val.2 = (3 : ℝ) ^ (-(depth Q : ℤ)))
    (hinside : ∀ Q ∈ Qfam, cubeSet Q ⊆ cubeSet ((0 : Vec d), (1 : ℝ)))
    (centers : ι → Finset (Vec d)) (j k : ℕ) (hj : 1 ≤ j)
    (haux : ∀ i, ∀ x ∈ centers i,
      cubeSet (x, (3 : ℝ) ^ (-(k : ℤ))) ⊆ cubeSet ((0 : Vec d), (1 : ℝ))) :
    ∃ (G : Finset (ℕ × Vec d)) (P : Finset (Cube d × Cube d)) (J N : ℕ),
      G.card ≤ N ∧ P.card ≤ N ∧ k ≤ J ∧
      (∀ q ∈ G, q.1 ≤ J ∧
        cubeSet (q.2, (3 : ℝ) ^ (-(q.1 : ℤ))) ⊆ cubeSet ((0 : Vec d), (1 : ℝ))) ∧
      (∀ Q : Qfam, (depth Q, Q.val.1) ∈ G) ∧
      (2, (0 : Vec d)) ∈ G ∧
      (∀ i, ∀ x ∈ centers i, (k, x) ∈ G) ∧
      P = goodCubeAuxiliaryPairs (goodCubeAuxiliaryCenterUnion centers) j (-(k : ℤ)) ∧
      ∀ p ∈ P, 0 < p.1.2 ∧ p.2.2 = (3 : ℝ) ^ (-(k : ℤ)) ∧
        p.1.2 = (3 : ℝ) ^ (-((j + k : ℕ) : ℤ)) ∧
        p.1.2 = (3 : ℝ) ^ (-(j : ℤ)) * p.2.2 ∧
        closure (cubeSet p.1) ⊆ centeredAxisCube p.2.1 (p.2.2 / 2) ∧
        cubeSet p.2 ⊆ cubeSet ((0 : Vec d), (1 : ℝ)) := by
  classical
  obtain ⟨G, J, hkJ, hG, hQ, hquarter, hauxG⟩ :=
    exists_goodCube_cube_test_catalog Qfam hfin depth hdepth hinside centers k haux
  set X : Finset (Vec d) := goodCubeAuxiliaryCenterUnion centers with hXdef
  have hX : ∀ x ∈ X, cubeSet (x, (3 : ℝ) ^ (-(k : ℤ))) ⊆
      cubeSet ((0 : Vec d), (1 : ℝ)) := by
    intro x hx
    rw [hXdef, mem_goodCube_auxiliary_center_union] at hx
    obtain ⟨i, hi⟩ := hx
    exact haux i x hi
  set P : Finset (Cube d × Cube d) :=
    goodCubeAuxiliaryPairs X j (-(k : ℤ)) with hPdef
  obtain ⟨hcard, hpair⟩ :=
    goodCube_auxiliary_reference_pair_catalog X j k hj hX
  refine ⟨G, P, J, max G.card P.card, le_max_left _ _, le_max_right _ _, hkJ,
    hG, hQ, hquarter, hauxG, hPdef, ?_⟩
  rw [hPdef]
  exact hpair

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
