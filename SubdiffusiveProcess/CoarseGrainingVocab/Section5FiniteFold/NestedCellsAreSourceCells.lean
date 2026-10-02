import SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily.NestedFamilyComplete

/-!
# The nested cells are one-step source cells

The complete nested two-radius family
(`Section5NeumannFamily/NestedFamilyComplete.lean`) indexes its cells by
`NFFullIndex d hd K j N`, and attaches to an index the cube

```
  nfNestedCell N q = translateCube (nfCellShift q.1.1 N) q.2.1,
```

the descendant `q.2.1` of the *origin* inner parent `originCube d (K - j - a)`
translated to the retained overlap centre `q.1.1`, where `a = depth + 1`.

Two purely combinatorial facts are proved here, and they are exactly what is
needed to feed the family's `delta ^ 68` readout into the source-cell average
of `DualCellMajorantInputs`:

* every nested cell is a depth-`j + N` descendant of the ambient cube, hence a
  one-step source cell as soon as `j + N = K - oneStepLocalizationScale`;
* the nested index is no larger than that descendant set, so normalizing by
  the source-cell cardinality only decreases the average.

The first is proved by identifying the *translated* inner parent with the
Calderón--Zygmund central descendant of the overlap centre — the index of a
central descendant is the parent index scaled by the triadic power, which is
precisely `nfCellShift` divided by the residual depth.  No measure theory and
no analysis enters.
-/

open MeasureTheory Homogenization
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily

noncomputable section

variable {d : ℕ}

/-- Extensionality for triadic cubes. -/
theorem nfCubeExt {A B : TriadicCube d}
    (hscale : A.scale = B.scale) (hindex : A.index = B.index) : A = B := by
  cases A
  cases B
  simp_all

/-- The inner origin parent, translated to a retained overlap centre, is the
Calderón--Zygmund central descendant of that centre. -/
theorem translateCube_originCube_eq_centralDescendant
    {K : ℤ} {j a : ℕ} (ha : 1 ≤ a) {S : TriadicCube d}
    (hS : S ∈ overlapCentersAtDepth (originCube d K) j) :
    translateCube (fun i ↦ (3 : ℤ) ^ (a - 1) * S.index i)
        (originCube d ((K - (j : ℤ)) - (a : ℤ))) =
      CubeCalderonZygmund.centralDescendant S (a - 1) := by
  have hSscale : S.scale + 1 = K - (j : ℤ) := nfOverlapCentre_scale hS
  refine (nfCubeExt ?_ ?_).symm
  · rw [CubeCalderonZygmund.centralDescendant_scale]
    simp only [translateCube, originCube]
    omega
  · funext i
    rw [CubeCalderonZygmund.centralDescendant_index]
    simp only [translateCube, originCube, Pi.zero_apply, zero_add]

/-- **Every nested cell is a depth-`j + N` descendant of the ambient cube.** -/
theorem nfNestedCell_mem_descendantsAtDepth
    {K : ℤ} {j N a k : ℕ} (ha : 1 ≤ a) (hak : a + k = N)
    (q : NFNestedIndex d K j (originCube d ((K - (j : ℤ)) - (a : ℤ))) k) :
    nfNestedCell N q ∈ descendantsAtDepth (originCube d K) (j + N) := by
  have hSmem : (q.1).1 ∈ overlapCentersAtDepth (originCube d K) j := (q.1).2
  have hSdesc : (q.1).1 ∈ descendantsAtDepth (originCube d K) (j + 1) :=
    mem_descendantsAtDepth_of_mem_overlapCentersAtDepth hSmem
  have hT := translateCube_originCube_eq_centralDescendant (K := K) (j := j)
    (a := a) ha hSmem
  have hpow : (3 : ℤ) ^ k * (3 : ℤ) ^ (a - 1) = (3 : ℤ) ^ (N - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hcellmem : nfNestedCell N q ∈
      descendantsAtDepth
        (translateCube (fun i ↦ (3 : ℤ) ^ (a - 1) * (q.1).1.index i)
          (originCube d ((K - (j : ℤ)) - (a : ℤ)))) k := by
    rw [descendantsAtDepth_translateCube]
    refine Finset.mem_image.mpr ⟨(q.2).1, (q.2).2, ?_⟩
    refine nfCubeExt rfl ?_
    funext i
    simp only [translateCube, descendantTranslationShift, nfNestedCell,
      nfCellShift]
    rw [← mul_assoc, hpow, mul_comm ((3 : ℤ) ^ (N - 1)) ((q.1).1.index i)]
  rw [hT] at hcellmem
  have h1 : nfNestedCell N q ∈
      descendantsAtDepth (q.1).1 ((a - 1) + k) :=
    mem_descendantsAtDepth_trans
      (CubeCalderonZygmund.centralDescendant_mem_descendantsAtDepth _ _)
      hcellmem
  have h2 : nfNestedCell N q ∈
      descendantsAtDepth (originCube d K) ((j + 1) + ((a - 1) + k)) :=
    mem_descendantsAtDepth_trans hSdesc h1
  have hidx : (j + 1) + ((a - 1) + k) = j + N := by omega
  rwa [hidx] at h2

/-- **The nested index is no larger than the depth-`j + N` descendant set.** -/
theorem nfNestedIndex_card_le_descendantsAtDepth_card
    {K : ℤ} {j N a k : ℕ} (ha : 1 ≤ a) (hak : a + k = N) :
    (Finset.univ : Finset
        (NFNestedIndex d K j
          (originCube d ((K - (j : ℤ)) - (a : ℤ))) k)).card ≤
      (descendantsAtDepth (originCube d K) (j + N)).card := by
  classical
  have hcardIndex :
      (Finset.univ : Finset
          (NFNestedIndex d K j
            (originCube d ((K - (j : ℤ)) - (a : ℤ))) k)).card =
        (overlapCentersAtDepth (originCube d K) j).card *
          (descendantsAtDepth
            (originCube d ((K - (j : ℤ)) - (a : ℤ))) k).card := by
    simp only [Finset.card_univ, NFNestedIndex, NFOverlapIndex,
      Fintype.card_prod, Fintype.card_coe]
  have hoverlap : (overlapCentersAtDepth (originCube d K) j).card ≤
      (3 ^ d) ^ (j + 1) := by
    rw [← descendantsAtDepth_card (originCube d K) (j + 1)]
    exact Finset.card_le_card fun S hS ↦
      mem_descendantsAtDepth_of_mem_overlapCentersAtDepth hS
  have hinner : (descendantsAtDepth
      (originCube d ((K - (j : ℤ)) - (a : ℤ))) k).card = (3 ^ d) ^ k :=
    descendantsAtDepth_card _ _
  have hsum : (j + 1) + k ≤ j + N := by omega
  calc
    _ = (overlapCentersAtDepth (originCube d K) j).card *
        (descendantsAtDepth
          (originCube d ((K - (j : ℤ)) - (a : ℤ))) k).card := hcardIndex
    _ ≤ (3 ^ d) ^ (j + 1) * (3 ^ d) ^ k := by
      rw [hinner]
      exact Nat.mul_le_mul_right _ hoverlap
    _ = (3 ^ d) ^ ((j + 1) + k) := (pow_add _ _ _).symm
    _ ≤ (3 ^ d) ^ (j + N) :=
      Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by norm_num)) hsum
    _ = (descendantsAtDepth (originCube d K) (j + N)).card :=
      (descendantsAtDepth_card _ _).symm

/-- **Coverage deficit of the nested index.**  Sharpening the previous bound:
the nested index is smaller than the source-cell set by at least the factor
`(3 ^ d) ^ (a - 1)`, where `a` is the Calderón--Zygmund interior depth of the
concentric parent.  Consequently the nested cells can occupy at most the
fraction `(3 ^ d) ^ -(a - 1)` of the depth-`j + N` descendants, and any
observable extended by zero off them vanishes on the rest. -/
theorem nfNestedIndex_card_mul_le_descendantsAtDepth_card
    {K : ℤ} {j N a k : ℕ} (ha : 1 ≤ a) (hak : a + k = N) :
    (Finset.univ : Finset
        (NFNestedIndex d K j
          (originCube d ((K - (j : ℤ)) - (a : ℤ))) k)).card *
        (3 ^ d) ^ (a - 1) ≤
      (descendantsAtDepth (originCube d K) (j + N)).card := by
  classical
  have hcardIndex :
      (Finset.univ : Finset
          (NFNestedIndex d K j
            (originCube d ((K - (j : ℤ)) - (a : ℤ))) k)).card =
        (overlapCentersAtDepth (originCube d K) j).card *
          (descendantsAtDepth
            (originCube d ((K - (j : ℤ)) - (a : ℤ))) k).card := by
    simp only [Finset.card_univ, NFNestedIndex, NFOverlapIndex,
      Fintype.card_prod, Fintype.card_coe]
  have hoverlap : (overlapCentersAtDepth (originCube d K) j).card ≤
      (3 ^ d) ^ (j + 1) := by
    rw [← descendantsAtDepth_card (originCube d K) (j + 1)]
    exact Finset.card_le_card fun S hS ↦
      mem_descendantsAtDepth_of_mem_overlapCentersAtDepth hS
  have hinner : (descendantsAtDepth
      (originCube d ((K - (j : ℤ)) - (a : ℤ))) k).card = (3 ^ d) ^ k :=
    descendantsAtDepth_card _ _
  have hexp : ((j + 1) + k) + (a - 1) = j + N := by omega
  calc
    _ = ((overlapCentersAtDepth (originCube d K) j).card *
        (descendantsAtDepth
          (originCube d ((K - (j : ℤ)) - (a : ℤ))) k).card) *
          (3 ^ d) ^ (a - 1) := by rw [hcardIndex]
    _ ≤ ((3 ^ d) ^ (j + 1) * (3 ^ d) ^ k) * (3 ^ d) ^ (a - 1) := by
      rw [hinner]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hoverlap)
    _ = (3 ^ d) ^ (((j + 1) + k) + (a - 1)) := by
      rw [← pow_add, ← pow_add]
    _ = (3 ^ d) ^ (j + N) := by rw [hexp]
    _ = (descendantsAtDepth (originCube d K) (j + N)).card :=
      (descendantsAtDepth_card _ _).symm

/-! ## Specialization to the family's own index -/

/-- Every cell of the complete nested family is a depth-`j + N` descendant of
the ambient cube. -/
theorem nfFullIndex_cell_mem_descendantsAtDepth
    (hd : 3 ≤ d) {K : ℤ} {j N : ℕ}
    (hN : nfAxisHarmonicDepth d hd + 1 ≤ N)
    (q : NFFullIndex d hd K j N) :
    nfNestedCell N q ∈ descendantsAtDepth (originCube d K) (j + N) :=
  nfNestedCell_mem_descendantsAtDepth (a := nfAxisHarmonicDepth d hd + 1)
    (Nat.le_add_left 1 _) (by omega) q

/-- The complete nested family's index is no larger than the depth-`j + N`
descendant set. -/
theorem nfFullIndex_card_le_descendantsAtDepth_card
    (hd : 3 ≤ d) {K : ℤ} {j N : ℕ}
    (hN : nfAxisHarmonicDepth d hd + 1 ≤ N) :
    (Finset.univ : Finset (NFFullIndex d hd K j N)).card ≤
      (descendantsAtDepth (originCube d K) (j + N)).card :=
  nfNestedIndex_card_le_descendantsAtDepth_card
    (a := nfAxisHarmonicDepth d hd + 1) (Nat.le_add_left 1 _) (by omega)

/-- The complete nested family's coverage deficit: its index is smaller than
the source-cell set by the factor `(3 ^ d) ^ nfAxisHarmonicDepth d hd`. -/
theorem nfFullIndex_card_mul_le_descendantsAtDepth_card
    (hd : 3 ≤ d) {K : ℤ} {j N : ℕ}
    (hN : nfAxisHarmonicDepth d hd + 1 ≤ N) :
    (Finset.univ : Finset (NFFullIndex d hd K j N)).card *
        (3 ^ d) ^ (nfAxisHarmonicDepth d hd) ≤
      (descendantsAtDepth (originCube d K) (j + N)).card := by
  have hbase := nfNestedIndex_card_mul_le_descendantsAtDepth_card
    (d := d) (K := K) (j := j) (N := N)
    (a := nfAxisHarmonicDepth d hd + 1) (k := N - (nfAxisHarmonicDepth d hd + 1))
    (Nat.le_add_left 1 _) (by omega)
  simpa only [Nat.add_sub_cancel] using hbase

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold
