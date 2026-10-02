import SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily.DescendantDirichletBudget

/-!
# Geometry of the nested cell family

The complete two-radius family indexes cells by a *pair*: a retained overlap
centre `S` (whose overlap cube is the concentric parent `P`, of scale
`S.scale + 1`) and a descendant `R₀` of the **origin** inner parent
`originCube d (mm - (depth+1))`.  The actual cell is `R₀` translated by
`cubeCenter S`, realized as a triadic cube by `translateCube`.

This module records the four geometric facts that indexing needs:

* descendant-depth transitivity;
* the central descendant of an origin cube is the smaller origin cube;
* `openCubeSet` of a `translateCube` is the translate of `openCubeSet`;
* the fixed concentric interior of a concentric parent is itself a concentric
  parent, one block of scales down.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily

open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-- Descendant depth is transitive. -/
theorem mem_descendantsAtDepth_trans {Q U R : TriadicCube d} {a : ℕ} :
    ∀ {k : ℕ}, U ∈ descendantsAtDepth Q a → R ∈ descendantsAtDepth U k →
      R ∈ descendantsAtDepth Q (a + k)
  | 0, hU, hR => by
      rw [descendantsAtDepth_zero, Finset.mem_singleton] at hR
      subst hR
      simpa using hU
  | k + 1, hU, hR => by
      rw [mem_descendantsAtDepth_succ_iff] at hR
      obtain ⟨T, hT, hRT⟩ := hR
      have hTQ : T ∈ descendantsAtDepth Q (a + k) :=
        mem_descendantsAtDepth_trans hU hT
      rw [show a + (k + 1) = (a + k) + 1 from rfl,
        mem_descendantsAtDepth_succ_iff]
      exact ⟨T, hTQ, hRT⟩

/-- The central descendant of an origin cube is the smaller origin cube. -/
theorem centralDescendant_originCube (d : ℕ) (m : ℤ) (a : ℕ) :
    CubeCalderonZygmund.centralDescendant (originCube d m) a =
      originCube d (m - (a : ℤ)) := by
  have hscale := CubeCalderonZygmund.centralDescendant_scale (originCube d m) a
  have hindex := CubeCalderonZygmund.centralDescendant_index (originCube d m)
  cases hC : CubeCalderonZygmund.centralDescendant (originCube d m) a with
  | mk scale index =>
      rw [hC] at hscale
      simp only [originCube] at hscale ⊢
      have hidx : index = 0 := by
        funext i
        have := hindex a i
        rw [hC] at this
        simpa [originCube] using this
      subst hidx
      simp only [TriadicCube.mk.injEq, and_true]
      exact hscale

/-- `openCubeSet` of a lattice translate is the translate of `openCubeSet`. -/
theorem openCubeSet_translateCube_eq (shift : Fin d → ℤ) (Q : TriadicCube d) :
    openCubeSet (translateCube shift Q) =
      translateSet (fun i => (shift i : ℝ) * cubeScaleFactor Q)
        (openCubeSet Q) := by
  ext x
  rw [mem_translateSet_iff_sub_mem, mem_openCubeSet_translateCube_iff]

/-- The fixed concentric interior of a concentric parent is the concentric
parent at scale `m - a`. -/
theorem nfAxisConcentric_eq_translate (d : ℕ) (z : Vec d) (m : ℤ) (a : ℕ) :
    axisCube
        (CubeCalderonZygmund.axisCubeConcentricDepthCorner
          (oneStepCenteredAxisCorner z m)
          (cubeScaleFactor (originCube d m)) a)
        (CubeCalderonZygmund.axisCubeConcentricDepthSide
          (cubeScaleFactor (originCube d m)) a) =
      translateSet z (openCubeSet (originCube d (m - (a : ℤ)))) := by
  have hthree : (3 : ℝ) ≠ 0 := by norm_num
  have hside : CubeCalderonZygmund.axisCubeConcentricDepthSide
      (cubeScaleFactor (originCube d m)) a =
      cubeScaleFactor (originCube d (m - (a : ℤ))) := by
    simp only [CubeCalderonZygmund.axisCubeConcentricDepthSide,
      cubeScaleFactor_originCube]
    rw [← zpow_add₀ hthree]
    congr 1
  have hcorner : CubeCalderonZygmund.axisCubeConcentricDepthCorner
      (oneStepCenteredAxisCorner z m)
      (cubeScaleFactor (originCube d m)) a =
      oneStepCenteredAxisCorner z (m - (a : ℤ)) := by
    funext i
    simp only [CubeCalderonZygmund.axisCubeConcentricDepthCorner,
      CubeCalderonZygmund.axisCubeCenter, oneStepCenteredAxisCorner, hside]
    ring
  rw [hcorner, hside, translateSet_openCubeSet_originCube_eq_axisCube]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily
