import SubdiffusiveProcess.Section10.InitialSimplexEnergyPacking

/-!
Finite maximal contained descendants. All cubes are actual triadic cubes.
The geometry is independent of coefficients and probability.
-/

namespace SubdiffusiveProcess.Section10

open Homogenization Homogenization.Book MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-- The depth-i cubes whose open interiors are contained, but whose parents
are not contained. Depth zero is excluded by the final finite union. -/
def maximalContainedAtDepth (R : TriadicCube d) (U : Set (Vec d)) (i : ℕ) :
    Finset (TriadicCube d) := by
  classical
  exact (descendantsAtDepth R i).filter fun Q =>
    openCubeSet Q ⊆ U ∧ ¬ openCubeSet (parentCube Q) ⊆ U

/-- The finite maximal packing, truncated at depth ell. -/
def maximalContainedPacking (R : TriadicCube d) (U : Set (Vec d)) (ell : ℕ) :
    Finset (TriadicCube d) :=
  (Finset.Icc 1 ell).biUnion (maximalContainedAtDepth R U)

/-- Unresolved finest cubes. Using the half-open cube in the intersection
makes the finite partition cover exact, including its grid faces. -/
def unresolvedAtDepth (R : TriadicCube d) (U : Set (Vec d)) (i : ℕ) :
    Finset (TriadicCube d) := by
  classical
  exact (descendantsAtDepth R i).filter fun Q =>
    (cubeSet Q ∩ U).Nonempty ∧ ¬ openCubeSet Q ⊆ U

@[simp] theorem mem_maximalContainedAtDepth {R Q : TriadicCube d}
    {U : Set (Vec d)} {i : ℕ} :
    Q ∈ maximalContainedAtDepth R U i ↔
      Q ∈ descendantsAtDepth R i ∧ openCubeSet Q ⊆ U ∧
        ¬ openCubeSet (parentCube Q) ⊆ U := by
  classical
  simp [maximalContainedAtDepth]

@[simp] theorem mem_maximalContainedPacking {R Q : TriadicCube d}
    {U : Set (Vec d)} {ell : ℕ} :
    Q ∈ maximalContainedPacking R U ell ↔
      ∃ i, 1 ≤ i ∧ i ≤ ell ∧ Q ∈ maximalContainedAtDepth R U i := by
  classical
  simp [maximalContainedPacking, Finset.mem_Icc, and_assoc]

@[simp] theorem mem_unresolvedAtDepth {R Q : TriadicCube d}
    {U : Set (Vec d)} {i : ℕ} :
    Q ∈ unresolvedAtDepth R U i ↔
      Q ∈ descendantsAtDepth R i ∧ (cubeSet Q ∩ U).Nonempty ∧
        ¬ openCubeSet Q ⊆ U := by
  classical
  simp [unresolvedAtDepth]

theorem parent_eq_of_mem_childCubes {P Q : TriadicCube d}
    (hQ : Q ∈ childCubes P) : parentCube Q = P := by
  obtain ⟨digits, rfl⟩ := mem_childCubes_iff.mp hQ
  exact childCube_parent P digits

theorem parent_mem_of_mem_descendants_succ {R Q : TriadicCube d} {i : ℕ}
    (hQ : Q ∈ descendantsAtDepth R (i + 1)) :
    parentCube Q ∈ descendantsAtDepth R i ∧ Q ∈ childCubes (parentCube Q) := by
  obtain ⟨P, hP, hQP⟩ := mem_descendantsAtDepth_succ_iff.mp hQ
  simpa only [parent_eq_of_mem_childCubes hQP] using And.intro hP hQP

/-- Two maximal contained cubes at any two positive depths have disjoint
half-open supports. This is stronger than the open-support interface. -/
theorem disjoint_maximalContainedAtDepth {R A B : TriadicCube d}
    {U : Set (Vec d)} {i j : ℕ}
    (hA : A ∈ maximalContainedAtDepth R U i)
    (hB : B ∈ maximalContainedAtDepth R U j) (hne : A ≠ B) :
    Disjoint (cubeSet A) (cubeSet B) := by
  classical
  wlog hij : i ≤ j generalizing A B i j
  · exact (this hB hA hne.symm (by omega)).symm
  obtain ⟨hAR, hAU, hAP⟩ := mem_maximalContainedAtDepth.mp hA
  obtain ⟨hBR, hBU, hBP⟩ := mem_maximalContainedAtDepth.mp hB
  have hBR' : B ∈ descendantsAtDepth R (i + (j - i)) := by
    simpa [Nat.add_sub_of_le hij] using hBR
  obtain ⟨C, hCR, hBC⟩ := exists_descendant_ancestor_at_depth i (j - i) hBR'
  by_cases hAC : A = C
  · subst C
    have hij' : i < j := by
      by_contra h
      have heq : i = j := by omega
      subst j
      simp only [Nat.sub_self, descendantsAtDepth_zero, Finset.mem_singleton] at hBC
      exact hne hBC.symm
    have hBC' : B ∈ descendantsAtDepth A ((j - i - 1) + 1) := by
      have heq : (j - i - 1) + 1 = j - i := by omega
      rw [heq]
      exact hBC
    have hPA := (parent_mem_of_mem_descendants_succ hBC').1
    exact (hBP ((openCubeSet_subset_of_mem_descendantsAtDepth hPA).trans hAU)).elim
  · exact (pairwiseDisjoint_descendantsAtDepth R i hAR hCR hAC).mono
      Set.Subset.rfl (cubeSet_subset_of_mem_descendantsAtDepth hBC)

theorem maximalContainedPacking_pairwiseDisjoint (R : TriadicCube d)
    (U : Set (Vec d)) (ell : ℕ) :
    (maximalContainedPacking R U ell : Set (TriadicCube d)).PairwiseDisjoint
      cubeSet := by
  intro A hA B hB hne
  obtain ⟨i, -, -, hAi⟩ := mem_maximalContainedPacking.mp hA
  obtain ⟨j, -, -, hBj⟩ := mem_maximalContainedPacking.mp hB
  exact disjoint_maximalContainedAtDepth hAi hBj hne

theorem maximalContainedPacking_pairwiseDisjoint_open (R : TriadicCube d)
    (U : Set (Vec d)) (ell : ℕ) :
    (maximalContainedPacking R U ell : Set (TriadicCube d)).PairwiseDisjoint
      openCubeSet := by
  intro A hA B hB hne
  exact (maximalContainedPacking_pairwiseDisjoint R U ell hA hB hne).mono
    (openCubeSet_subset_cubeSet A) (openCubeSet_subset_cubeSet B)

theorem maximalContainedPacking_subset {R Q : TriadicCube d}
    {U : Set (Vec d)} {ell : ℕ} (hQ : Q ∈ maximalContainedPacking R U ell) :
    openCubeSet Q ⊆ U := by
  obtain ⟨i, -, -, hQi⟩ := mem_maximalContainedPacking.mp hQ
  exact (mem_maximalContainedAtDepth.mp hQi).2.1

/-- Every simplex point is in a packed half-open cube or in an unresolved
finest cube. No infinite packing or limiting cover is used. -/
theorem maximalContainedPacking_cover {R : TriadicCube d} {U : Set (Vec d)}
    (hUR : U ⊆ cubeSet R) (hroot : ¬ openCubeSet R ⊆ U) (ell : ℕ) :
    U ⊆ (⋃ Q ∈ maximalContainedPacking R U ell, cubeSet Q) ∪
      ⋃ Q ∈ unresolvedAtDepth R U ell, cubeSet Q := by
  classical
  intro x hx
  obtain ⟨Q, hQR, hxQ⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet ell (hUR hx)
  by_cases hQU : openCubeSet Q ⊆ U
  · let P : ℕ → Prop := fun i => ∃ A ∈ descendantsAtDepth R i,
        x ∈ cubeSet A ∧ openCubeSet A ⊆ U
    have hex : ∃ i, P i := ⟨ell, Q, hQR, hxQ, hQU⟩
    have hmin : P (Nat.find hex) := Nat.find_spec hex
    obtain ⟨A, hAR, hxA, hAU⟩ := hmin
    have hpos : 0 < Nat.find hex := by
      by_contra h
      have hz : Nat.find hex = 0 := by omega
      rw [hz, descendantsAtDepth_zero, Finset.mem_singleton] at hAR
      subst A
      exact hroot hAU
    have hpar : parentCube A ∈ descendantsAtDepth R (Nat.find hex - 1) ∧
        A ∈ childCubes (parentCube A) := by
      apply parent_mem_of_mem_descendants_succ
      have heq : (Nat.find hex - 1) + 1 = Nat.find hex := by omega
      rw [heq]
      exact hAR
    have hparent : ¬ openCubeSet (parentCube A) ⊆ U := by
      intro hp
      exact Nat.find_min hex (by omega)
        ⟨parentCube A, hpar.1, cubeSet_subset_of_mem_childCubes hpar.2 hxA, hp⟩
    apply Or.inl
    exact Set.mem_iUnion₂.mpr ⟨A, mem_maximalContainedPacking.mpr
      ⟨Nat.find hex, hpos, Nat.find_min' hex ⟨Q, hQR, hxQ, hQU⟩,
        mem_maximalContainedAtDepth.mpr ⟨hAR, hAU, hparent⟩⟩, hxA⟩
  · apply Or.inr
    exact Set.mem_iUnion₂.mpr ⟨Q,
      mem_unresolvedAtDepth.mpr ⟨hQR, ⟨x, hxQ, hx⟩, hQU⟩, hxQ⟩

/-- Every retained depth-(i+1) cube comes from an unresolved depth-i parent. -/
theorem maximalContainedAtDepth_subset_children_unresolved (R : TriadicCube d)
    (U : Set (Vec d)) (i : ℕ) :
    maximalContainedAtDepth R U (i + 1) ⊆
      (unresolvedAtDepth R U i).biUnion childCubes := by
  classical
  intro Q hQ
  obtain ⟨hQR, hQU, hQP⟩ := mem_maximalContainedAtDepth.mp hQ
  obtain ⟨hPR, hQC⟩ := parent_mem_of_mem_descendants_succ hQR
  have hx : (openCubeSet Q).Nonempty := by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact ⟨cubeCenter Q, Metric.mem_ball_self (cubeRadius_pos Q)⟩
  obtain ⟨x, hxQ⟩ := hx
  refine Finset.mem_biUnion.mpr ⟨parentCube Q, ?_, hQC⟩
  exact mem_unresolvedAtDepth.mpr ⟨hPR,
    ⟨x, cubeSet_subset_of_mem_childCubes hQC (openCubeSet_subset_cubeSet Q hxQ),
      hQU hxQ⟩, hQP⟩

theorem maximalContainedAtDepth_card_le (R : TriadicCube d)
    (U : Set (Vec d)) (i : ℕ) :
    (maximalContainedAtDepth R U (i + 1)).card ≤
      (unresolvedAtDepth R U i).card * 3 ^ d := by
  classical
  calc
    _ ≤ ((unresolvedAtDepth R U i).biUnion childCubes).card :=
      Finset.card_le_card (maximalContainedAtDepth_subset_children_unresolved R U i)
    _ ≤ ∑ Q ∈ unresolvedAtDepth R U i, (childCubes Q).card := Finset.card_biUnion_le
    _ = _ := by simp [childCubes_card]

/-- Recover a cube's natural depth from its scale. -/
def packingCubeDepth (R Q : TriadicCube d) : ℕ := (R.scale - Q.scale).toNat

theorem packingCubeDepth_eq {R Q : TriadicCube d} {i : ℕ}
    (hQ : Q ∈ descendantsAtDepth R i) : packingCubeDepth R Q = i := by
  rw [packingCubeDepth, scale_eq_sub_of_mem_descendantsAtDepth hQ]
  simp

theorem maximalContainedPacking_depth_bounds {R Q : TriadicCube d}
    {U : Set (Vec d)} {ell : ℕ} (hQ : Q ∈ maximalContainedPacking R U ell) :
    0 < packingCubeDepth R Q ∧ packingCubeDepth R Q ≤ ell ∧
      Q.scale = R.scale - (packingCubeDepth R Q : ℤ) := by
  obtain ⟨i, hi, hiell, hQi⟩ := mem_maximalContainedPacking.mp hQ
  have hQR := (mem_maximalContainedAtDepth.mp hQi).1
  rw [packingCubeDepth_eq hQR]
  exact ⟨hi, hiell, scale_eq_sub_of_mem_descendantsAtDepth hQR⟩

theorem maximalContainedPacking_filter_depth (R : TriadicCube d)
    (U : Set (Vec d)) (ell i : ℕ) (hi : 1 ≤ i) (hiell : i ≤ ell) :
    (maximalContainedPacking R U ell).filter (fun Q => packingCubeDepth R Q = i) =
      maximalContainedAtDepth R U i := by
  classical
  ext Q
  constructor
  · intro hQ
    obtain ⟨hQP, hdepth⟩ := Finset.mem_filter.mp hQ
    obtain ⟨j, -, -, hQj⟩ := mem_maximalContainedPacking.mp hQP
    have hj : packingCubeDepth R Q = j :=
      packingCubeDepth_eq (mem_maximalContainedAtDepth.mp hQj).1
    have heq : j = i := hj.symm.trans hdepth
    simpa only [heq] using hQj
  · intro hQ
    exact Finset.mem_filter.mpr ⟨mem_maximalContainedPacking.mpr ⟨i, hi, hiell, hQ⟩,
      packingCubeDepth_eq (mem_maximalContainedAtDepth.mp hQ).1⟩

end
end SubdiffusiveProcess.Section10
