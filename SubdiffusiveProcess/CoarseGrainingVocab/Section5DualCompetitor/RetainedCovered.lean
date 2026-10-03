module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor.UncoveredFraction
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold.RetainedParentCovering

@[expose] public section

/-!
# The committed retained cells are covered by the overlap-centre family

`card_sdiff_div_card_le_uncoveredFractionBound` (`UncoveredFraction.lean`)
needs `oneStepRetainedSourceCells … ⊆ covered`, where `covered` is P-121c's
family: the source cells lying inside a *retained overlap centre*
(`overlapCentersAtDepth Q j` filters the depth-`(j+1)` descendants by
`overlapCubeSet S ⊆ cubeSet Q`, and `overlapCubeSet` is the `3×` dilate).

This module supplies that inclusion, at auxiliary radius `N + 1`.  The
arithmetic is comfortable: writing `sf` for `cubeScaleFactor S`, the ancestor
`S` of a source cell `R` at depth `j + 1` has

```text
overlapCubeSet S ⊆ { x | ∀ i, |x i - cubeCenter S i| ≤ (3/2) · sf },
cubeCenter R ∈ openCubeSet S ⊆ { x | ∀ i, |x i - cubeCenter S i| < (1/2) · sf },
```

so every point of `overlapCubeSet S` is within `2 · sf` of `cubeCenter R`,
while `oneStepCenteredParent (cubeCenter R) (source + N + 1)` has half-width
`(9/2) · sf`.  Hence the retained condition at radius `N + 1` — which puts
that centred parent inside the cube — already forces
`overlapCubeSet S ⊆ cubeSet Q`.

The one genuinely missing combinatorial step is the *splitting* direction of
`mem_descendantsAtDepth_add`: only the forward composition is committed.
-/

open MeasureTheory Homogenization Homogenization.Book Filter
open scoped BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold

noncomputable section

variable {d : ℕ}



theorem exists_mem_descendantsAtDepth_split
    {Q R : TriadicCube d} {a b : ℕ}
    (hR : R ∈ descendantsAtDepth Q (a + b)) :
    ∃ S ∈ descendantsAtDepth Q a, R ∈ descendantsAtDepth S b := by
  induction b generalizing R with
  | zero =>
      refine ⟨R, by simpa using hR, ?_⟩
      rw [descendantsAtDepth_zero]
      exact Finset.mem_singleton_self R
  | succ b ih =>
      rw [show a + (b + 1) = (a + b) + 1 from by omega,
        mem_descendantsAtDepth_succ_iff] at hR
      obtain ⟨T, hT, hchild⟩ := hR
      obtain ⟨S, hS, hTS⟩ := ih hT
      exact ⟨S, hS, mem_descendantsAtDepth_succ_iff.mpr ⟨T, hTS, hchild⟩⟩

/-- The `3×` dilate of a cube lies within `2 · cubeScaleFactor S` of the
centre of any subcube. -/
theorem overlapCubeSet_subset_oneStepCenteredParent
    {S R : TriadicCube d} {m : ℤ}
    (hRS : openCubeSet R ⊆ openCubeSet S)
    (hm : cubeScaleFactor (originCube d m) = 9 * cubeScaleFactor S) :
    overlapCubeSet S ⊆ oneStepCenteredParent (cubeCenter R) m := by
  have hsf : (0 : ℝ) < cubeScaleFactor S := by
    simpa [cubeScaleFactor] using
      (zpow_pos (by norm_num : (0 : ℝ) < 3) S.scale)
  have hcenter : cubeCenter R ∈ openCubeSet S :=
    hRS (cubeCenter_mem_openCubeSet R)
  intro x hx
  rw [mem_oneStepCenteredParent_iff]
  intro i
  have hxi := hx i
  have hci := hcenter i
  rw [hm]
  simp only [cubeCenter] at hci ⊢
  constructor <;> nlinarith [hxi.1, hxi.2, hci.1, hci.2, hsf]

/-- **The inclusion.**  Every source cell whose `(N + 1)`-enlarged centred
parent stays inside the cube lies inside a retained overlap centre. -/
theorem oneStepRetainedSourceCells_subset_overlapCentreCovered
    {K n : ℕ} {delta : ℝ} {j N : ℕ}
    (hsource : oneStepLocalizationScale n delta ≤ K)
    (hN : 1 ≤ N)
    (hjN : j + N = K - oneStepLocalizationScale n delta) :
    oneStepRetainedSourceCells (d := d) (K : ℤ)
        (oneStepLocalizationScale n delta : ℤ) (N + 1) ⊆
      (oneStepSourceCells d K n delta).filter (fun R ↦
        ∃ S ∈ overlapCentersAtDepth (originCube d (K : ℤ)) j,
          R ∈ descendantsAtDepth S (N - 1)) := by
  classical
  set ls : ℕ := oneStepLocalizationScale n delta with hls
  set Q : TriadicCube d := originCube d (K : ℤ) with hQ
  intro R hR
  obtain ⟨hRscale, hRpar⟩ := mem_oneStepRetainedSourceCells_iff.mp hR
  -- `R` is a source cell
  have hlsK : (ls : ℤ) ≤ (K : ℤ) := by exact_mod_cast hsource
  have hQscale : Q.scale = (K : ℤ) := by simp [hQ, originCube]
  have htoNat : Int.toNat (Q.scale - (ls : ℤ)) = K - ls := by
    rw [hQscale]; omega
  have hRsrc : R ∈ oneStepSourceCells d K n delta := by
    rw [descendantsAtScale_eq_descendantsAtDepth Q (by rw [hQscale]; exact hlsK),
      htoNat] at hRscale
    exact hRscale
  refine Finset.mem_filter.mpr ⟨hRsrc, ?_⟩
  -- split the depth `j + N` as `(j + 1) + (N - 1)`
  have hdepth : R ∈ descendantsAtDepth Q ((j + 1) + (N - 1)) := by
    have : (j + 1) + (N - 1) = K - ls := by omega
    rw [this]
    exact hRsrc
  obtain ⟨S, hS, hRS⟩ := exists_mem_descendantsAtDepth_split hdepth
  refine ⟨S, ?_, hRS⟩
  -- `S` is a retained overlap centre
  rw [mem_overlapCentersAtDepth_iff]
  refine ⟨hS, ?_⟩
  have hSscale : S.scale = (K : ℤ) - ((j : ℤ) + 1) := by
    have := scale_eq_sub_of_mem_descendantsAtDepth hS
    rw [hQscale] at this
    rw [this]; push_cast; ring
  have hsf9 : cubeScaleFactor (originCube d ((ls : ℤ) + ((N + 1 : ℕ) : ℤ))) =
      9 * cubeScaleFactor S := by
    have hexp : ((ls : ℤ) + ((N + 1 : ℕ) : ℤ)) = S.scale + 2 := by
      rw [hSscale]; push_cast; omega
    simp only [cubeScaleFactor, originCube, hexp]
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    ring
  have hRSopen : openCubeSet R ⊆ openCubeSet S :=
    openCubeSet_subset_of_mem_descendantsAtDepth hRS
  have hsub := overlapCubeSet_subset_oneStepCenteredParent hRSopen hsf9
  refine (hsub.trans hRpar).trans ?_
  intro x hx i
  exact ⟨(hx i).1.le, (hx i).2⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor
