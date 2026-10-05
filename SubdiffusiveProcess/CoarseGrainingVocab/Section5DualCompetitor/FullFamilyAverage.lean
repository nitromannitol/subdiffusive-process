module

public import SubdiffusiveProcess.CoarseGrainingVocab.CaccioppoliRHS
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepRetainedNeumannGluing

@[expose] public section




open MeasureTheory Homogenization
open scoped BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor

noncomputable section

variable {d : ℕ}

/-- An `openCubeSet` integrability hypothesis transports to `cubeSet`: the two
sets differ by a Lebesgue-null set of faces. -/
theorem integrableOn_cubeSet_of_integrableOn_openCubeSet
    (Q : TriadicCube d) {g : Vec d → ℝ}
    (hg : IntegrableOn g (openCubeSet Q)) :
    IntegrableOn g (cubeSet Q) := by
  simpa only [IntegrableOn,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using hg

/-- **The full-family cell decomposition.**  For the *complete* descendant
family at a fixed depth the parent average is exactly the normalized sum of
the cell averages — no boundary strip. -/
theorem volumeAverage_eq_normalized_descendantsAtDepth_sum
    (Q : TriadicCube d) (j : ℕ) {g : Vec d → ℝ}
    (hg : IntegrableOn g (openCubeSet Q)) :
    volumeAverage (openCubeSet Q) g =
      (((descendantsAtDepth Q j).card : ℝ)⁻¹) *
        ∑ R ∈ descendantsAtDepth Q j, volumeAverage (openCubeSet R) g := by
  rw [volumeAverage_openCubeSet_eq_cubeAverage Q g,
    cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q j g
      (integrableOn_cubeSet_of_integrableOn_openCubeSet Q hg)]
  unfold descendantsAverage
  refine congrArg (fun z ↦ (((descendantsAtDepth Q j).card : ℝ)⁻¹) * z) ?_
  exact Finset.sum_congr rfl fun R _hR ↦
    (volumeAverage_openCubeSet_eq_cubeAverage R g).symm

/-- Inequality form, matching the shape of
`le_normalized_cellSum_add_boundary` with the boundary summand replaced by the
constant `0`, and with the cellwise values rewritten through `T`. -/
theorem le_normalized_descendantsAtDepth_cellSum
    (Q : TriadicCube d) (j : ℕ) {g : Vec d → ℝ} (T : TriadicCube d → ℝ)
    (hg : IntegrableOn g (openCubeSet Q))
    (hsplit : ∀ R ∈ descendantsAtDepth Q j,
      volumeAverage (openCubeSet R) g = T R)
    {target : ℝ}
    (hcompetitor : target ≤ volumeAverage (openCubeSet Q) g) :
    target ≤ (((descendantsAtDepth Q j).card : ℝ)⁻¹) *
      ∑ R ∈ descendantsAtDepth Q j, T R := by
  refine hcompetitor.trans_eq ?_
  rw [volumeAverage_eq_normalized_descendantsAtDepth_sum Q j hg]
  exact congrArg (fun z ↦ (((descendantsAtDepth Q j).card : ℝ)⁻¹) * z)
    (Finset.sum_congr rfl hsplit)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor
