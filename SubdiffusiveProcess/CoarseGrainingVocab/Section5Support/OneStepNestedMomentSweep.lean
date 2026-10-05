module

public import SubdiffusiveProcess.Analysis.RawLp

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNestedRecentering
public import Homogenization.Deterministic.ConstantCoefficientDirichletBesov.OverlapCenters
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.DirichletEndpoint
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.NeumannEndpoint

@[expose] public section

/-!
# Finite-overlap moment sweep for nested one-step solutions

This module supplies the probability-free overlap step.  The fourth power of each
normalized local `L²` norm is first bounded by the normalized local `L⁴`
mass.  The retained overlap cubes then cost only their pointwise
multiplicity `3^d`.

The geometric multiplicity is supplied by CoarseGraining's `overlapCentersAtDepth` API.
-/

open MeasureTheory Homogenization
open scoped ENNReal NNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- The open overlap cube is exactly the centered translate of the next
triadic scale. -/
theorem openOverlapCubeSet_eq_translateSet_originCube_succ
    {d : ℕ} (S : TriadicCube d) :
    openOverlapCubeSet S =
      translateSet (cubeCenter S) (openCubeSet (originCube d (S.scale + 1))) := by
  rw [openOverlapCubeSet_eq_translateSet_smul_originCube_zero,
    overlapCubeScaleFactor_eq_cubeScaleFactor_originCube_succ,
    ← openCubeSet_originCube_eq_smul_unit d (S.scale + 1)]

/-- The normalized overlap measure is the exact normalized axis-cube measure
used by the arbitrary-center harmonic package. -/
theorem normalizedOverlapCubeMeasure_eq_axisCubeNormalizedMeasure
    {d : ℕ} (S : TriadicCube d) :
    normalizedOverlapCubeMeasure S =
      CubeCalderonZygmund.axisCubeNormalizedMeasure
        (oneStepCenteredAxisCorner (cubeCenter S) (S.scale + 1))
        (cubeScaleFactor (originCube d (S.scale + 1))) := by
  have hside : 0 < cubeScaleFactor (originCube d (S.scale + 1)) := by
    simpa [cubeScaleFactor] using!
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) (S.scale + 1))
  rw [CubeCalderonZygmund.axisCubeNormalizedMeasure_eq_smul_volume_restrict
    _ _ hside]
  unfold normalizedOverlapCubeMeasure overlapCubeMeasure overlapCubeVolume
  rw [volume_restrict_overlapCubeSet_eq_volume_restrict_openOverlapCubeSet,
    openOverlapCubeSet_eq_translateSet_originCube_succ,
    translateSet_openCubeSet_originCube_eq_axisCube,
    overlapCubeScaleFactor_eq_cubeScaleFactor_originCube_succ]

/-- The axis-cube norm of the actual Dirichlet large restriction is exactly
the overlap-cube norm of the global solution gradient. -/
theorem eLpNorm_oneStepDirichletAxisLargeRestriction_eq_overlap
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p : Vec d) (K : ℤ) (S : TriadicCube d)
    (hsub : translateSet (cubeCenter S)
        (openCubeSet (originCube d (S.scale + 1))) ⊆
      openCubeSet (originCube d K)) (hh : 0 < h) :
    eLpNorm
        (hilbertifyVecField
          (oneStepDirichletAxisLargeRestriction M n h omega p
            (cubeCenter S) K (S.scale + 1) hsub hh).grad)
        2
        (CubeCalderonZygmund.axisCubeNormalizedMeasure
          (oneStepCenteredAxisCorner (cubeCenter S) (S.scale + 1))
          (cubeScaleFactor (originCube d (S.scale + 1)))) =
      eLpNorm
        (hilbertifyVecField
          (oneStepOriginDirichletSolution M n h p K omega hh).toH1Function.grad)
        2 (normalizedOverlapCubeMeasure S) := by
  rw [← normalizedOverlapCubeMeasure_eq_axisCubeNormalizedMeasure S]
  rw [oneStepDirichletAxisLargeRestriction_grad]

/-- Neumann version of the exact overlap-cube norm readout. -/
theorem eLpNorm_oneStepNeumannAxisLargeRestriction_eq_overlap
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p : Vec d) (K : ℤ) (S : TriadicCube d)
    (hsub : translateSet (cubeCenter S)
        (openCubeSet (originCube d (S.scale + 1))) ⊆
      openCubeSet (originCube d K)) (hh : 0 < h) :
    eLpNorm
        (hilbertifyVecField
          (oneStepNeumannAxisLargeRestriction M n h omega p
            (cubeCenter S) K (S.scale + 1) hsub hh).grad)
        2
        (CubeCalderonZygmund.axisCubeNormalizedMeasure
          (oneStepCenteredAxisCorner (cubeCenter S) (S.scale + 1))
          (cubeScaleFactor (originCube d (S.scale + 1)))) =
      eLpNorm
        (hilbertifyVecField
          (oneStepOriginNeumannSolution M n h p K omega hh).toH1Function.grad)
        2 (normalizedOverlapCubeMeasure S) := by
  rw [← normalizedOverlapCubeMeasure_eq_axisCubeNormalizedMeasure S]
  rw [oneStepNeumannAxisLargeRestriction_grad]

/-- Every retained overlap parent is an open subdomain of its outer cube in
the centered-translate convention used by the solution operator. -/
theorem oneStepOverlapParent_subset_outerCube
    {d : ℕ} {Q S : TriadicCube d} {j : ℕ}
    (hS : S ∈ overlapCentersAtDepth Q j) :
    translateSet (cubeCenter S)
        (openCubeSet (originCube d (S.scale + 1))) ⊆ openCubeSet Q := by
  rw [← openOverlapCubeSet_eq_translateSet_originCube_succ]
  exact openOverlapCubeSet_subset_openCubeSet_of_mem_overlapCentersAtDepth hS

/-- Literal axis-cube Dirichlet large-restriction norm, extended by zero away
from the retained overlap family so it can be summed as an ordinary finite
observable. -/
noncomputable def oneStepDirichletOverlapLargeGradient
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (K : ℤ) (j : ℕ) (S : TriadicCube d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) : ℝ≥0∞ :=
  if hS : S ∈ overlapCentersAtDepth (originCube d K) j then
    eLpNorm
      (hilbertifyVecField
        (oneStepDirichletAxisLargeRestriction M n h omega p
          (cubeCenter S) K (S.scale + 1)
          (oneStepOverlapParent_subset_outerCube hS) hh).grad)
      2
      (CubeCalderonZygmund.axisCubeNormalizedMeasure
        (oneStepCenteredAxisCorner (cubeCenter S) (S.scale + 1))
        (cubeScaleFactor (originCube d (S.scale + 1))))
  else 0

/-- Neumann counterpart of the zero-extended overlap observable. -/
noncomputable def oneStepNeumannOverlapLargeGradient
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (K : ℤ) (j : ℕ) (S : TriadicCube d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) : ℝ≥0∞ :=
  if hS : S ∈ overlapCentersAtDepth (originCube d K) j then
    eLpNorm
      (hilbertifyVecField
        (oneStepNeumannAxisLargeRestriction M n h omega p
          (cubeCenter S) K (S.scale + 1)
          (oneStepOverlapParent_subset_outerCube hS) hh).grad)
      2
      (CubeCalderonZygmund.axisCubeNormalizedMeasure
        (oneStepCenteredAxisCorner (cubeCenter S) (S.scale + 1))
        (cubeScaleFactor (originCube d (S.scale + 1))))
  else 0

theorem oneStepDirichletOverlapLargeGradient_eq
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (K : ℤ) (j : ℕ) (S : TriadicCube d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    (hS : S ∈ overlapCentersAtDepth (originCube d K) j) :
    oneStepDirichletOverlapLargeGradient M n h p K j S omega hh =
      eLpNorm
        (hilbertifyVecField
          (oneStepOriginDirichletSolution
            M n h p K omega hh).toH1Function.grad)
        2 (normalizedOverlapCubeMeasure S) := by
  rw [oneStepDirichletOverlapLargeGradient, dite_eq_left hS,
    eLpNorm_oneStepDirichletAxisLargeRestriction_eq_overlap]

theorem oneStepNeumannOverlapLargeGradient_eq
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (K : ℤ) (j : ℕ) (S : TriadicCube d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    (hS : S ∈ overlapCentersAtDepth (originCube d K) j) :
    oneStepNeumannOverlapLargeGradient M n h p K j S omega hh =
      eLpNorm
        (hilbertifyVecField
          (oneStepOriginNeumannSolution
            M n h p K omega hh).toH1Function.grad)
        2 (normalizedOverlapCubeMeasure S) := by
  rw [oneStepNeumannOverlapLargeGradient, dite_eq_left hS,
    eLpNorm_oneStepNeumannAxisLargeRestriction_eq_overlap]

/-! ## Stationary local member of every recentering level -/

/-- Fourth power of the stationary Dirichlet solution subtracted on an
overlap parent.  The definition is zero away from the retained family, so it
can be combined termwise with `oneStepDirichletOverlapLargeGradient`. -/
noncomputable def oneStepDirichletOverlapLocalGradientFourth
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (K : ℤ) (j : ℕ) (S : TriadicCube d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) : ℝ≥0∞ :=
  if _hS : S ∈ overlapCentersAtDepth (originCube d K) j then
    ENNReal.ofReal
      (oneStepTranslatedDirichletNormalizedGradientFourth
        M n h p (cubeCenter S) (S.scale + 1) omega hh)
  else 0

/-- Neumann counterpart of the stationary local fourth-power observable. -/
noncomputable def oneStepNeumannOverlapLocalGradientFourth
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (K : ℤ) (j : ℕ) (S : TriadicCube d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) : ℝ≥0∞ :=
  if _hS : S ∈ overlapCentersAtDepth (originCube d K) j then
    ENNReal.ofReal
      (oneStepTranslatedNeumannNormalizedGradientFourth
        M n h p (cubeCenter S) (S.scale + 1) omega hh)
  else 0

theorem measurable_oneStepDirichletOverlapLocalGradientFourth
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (K : ℤ) (j : ℕ) (S : TriadicCube d) (hh : 0 < h) :
    Measurable
      (fun omega ↦ oneStepDirichletOverlapLocalGradientFourth
        M n h p K j S omega hh) := by
  unfold oneStepDirichletOverlapLocalGradientFourth
  split_ifs
  · exact ENNReal.continuous_ofReal.measurable.comp
      (measurable_oneStepTranslatedDirichletNormalizedGradientFourth
        M n h p (cubeCenter S) (S.scale + 1) hh)
  · exact measurable_const

theorem measurable_oneStepNeumannOverlapLocalGradientFourth
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (K : ℤ) (j : ℕ) (S : TriadicCube d) (hh : 0 < h) :
    Measurable
      (fun omega ↦ oneStepNeumannOverlapLocalGradientFourth
        M n h p K j S omega hh) := by
  unfold oneStepNeumannOverlapLocalGradientFourth
  split_ifs
  · exact ENNReal.continuous_ofReal.measurable.comp
      (measurable_oneStepTranslatedNeumannNormalizedGradientFourth
        M n h p (cubeCenter S) (S.scale + 1) hh)
  · exact measurable_const

/-- Each stationary Dirichlet recentering member has the uniform fourth
moment inherited from the origin solution law. -/
theorem lintegral_oneStepDirichletOverlapLocalGradientFourth_le_uniform
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (K : ℤ) (j : ℕ) (S : TriadicCube d)
    (hh : 0 < h) (hp : vecNormSq p = 1)
    (hblock : (h : ℝ) ≤ M.delta⁻¹) :
    ∫⁻ omega, oneStepDirichletOverlapLocalGradientFourth
        M n h p K j S omega hh ∂M.P.toMeasure ≤
      ENNReal.ofReal (oneStepSourceParentGradientConst ^ (4 : ℕ)) := by
  by_cases hS : S ∈ overlapCentersAtDepth (originCube d K) j
  · rw [show (fun omega ↦ oneStepDirichletOverlapLocalGradientFourth
          M n h p K j S omega hh) =
        fun omega ↦ ENNReal.ofReal
          (oneStepTranslatedDirichletNormalizedGradientFourth
            M n h p (cubeCenter S) (S.scale + 1) omega hh) by
      funext omega
      simp [oneStepDirichletOverlapLocalGradientFourth, hS]]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_oneStepTranslatedDirichletNormalizedGradientFourth M n h p
        (cubeCenter S) (S.scale + 1) hh
        (integrable_oneStepOriginDirichletNormalizedGradientFourth_uniform
          M n h p (S.scale + 1) hh hp))
      (Filter.Eventually.of_forall fun omega ↦ by
        unfold oneStepTranslatedDirichletNormalizedGradientFourth
        positivity)]
    exact ENNReal.ofReal_le_ofReal
      (integral_oneStepTranslatedDirichletNormalizedGradientFourth_le_uniform
        M n h p (cubeCenter S) (S.scale + 1) hh hp hblock)
  · simp [oneStepDirichletOverlapLocalGradientFourth, hS]

/-- Neumann version of the uniform stationary-member moment. -/
theorem lintegral_oneStepNeumannOverlapLocalGradientFourth_le_uniform
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (K : ℤ) (j : ℕ) (S : TriadicCube d)
    (hh : 0 < h) (hp : vecNormSq p = 1)
    (hblock : (h : ℝ) ≤ M.delta⁻¹) :
    ∫⁻ omega, oneStepNeumannOverlapLocalGradientFourth
        M n h p K j S omega hh ∂M.P.toMeasure ≤
      ENNReal.ofReal (oneStepSourceParentGradientConst ^ (4 : ℕ)) := by
  by_cases hS : S ∈ overlapCentersAtDepth (originCube d K) j
  · rw [show (fun omega ↦ oneStepNeumannOverlapLocalGradientFourth
          M n h p K j S omega hh) =
        fun omega ↦ ENNReal.ofReal
          (oneStepTranslatedNeumannNormalizedGradientFourth
            M n h p (cubeCenter S) (S.scale + 1) omega hh) by
      funext omega
      simp [oneStepNeumannOverlapLocalGradientFourth, hS]]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_oneStepTranslatedNeumannNormalizedGradientFourth M n h p
        (cubeCenter S) (S.scale + 1) hh
        (integrable_oneStepOriginNeumannNormalizedGradientFourth_uniform
          M n h p (S.scale + 1) hh hp))
      (Filter.Eventually.of_forall fun omega ↦ by
        unfold oneStepTranslatedNeumannNormalizedGradientFourth
        positivity)]
    exact ENNReal.ofReal_le_ofReal
      (integral_oneStepTranslatedNeumannNormalizedGradientFourth_le_uniform
        M n h p (cubeCenter S) (S.scale + 1) hh hp hblock)
  · simp [oneStepNeumannOverlapLocalGradientFourth, hS]

/-- Normalized finite-overlap average of all stationary Dirichlet members.
The bound is independent of the nesting depth and of the outer cube. -/
theorem lintegral_average_oneStepDirichletOverlapLocalGradientFourth_le_uniform
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (K : ℤ) (j : ℕ) (hh : 0 < h)
    (hp : vecNormSq p = 1) (hblock : (h : ℝ) ≤ M.delta⁻¹) :
    ∫⁻ omega,
        (((overlapCentersAtDepth (originCube d K) j).card : ℝ≥0∞)⁻¹) *
          (∑ S ∈ overlapCentersAtDepth (originCube d K) j,
            oneStepDirichletOverlapLocalGradientFourth
              M n h p K j S omega hh)
        ∂M.P.toMeasure ≤
      ENNReal.ofReal (oneStepSourceParentGradientConst ^ (4 : ℕ)) := by
  let s := overlapCentersAtDepth (originCube d K) j
  let B : ℝ≥0∞ := ENNReal.ofReal (oneStepSourceParentGradientConst ^ (4 : ℕ))
  have hs : s.Nonempty := overlapCentersAtDepth_nonempty _ _
  have hcard0 : (s.card : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hs.card_ne_zero
  have hcardTop : (s.card : ℝ≥0∞) ≠ ∞ := by finiteness
  calc
    (∫⁻ omega, ((s.card : ℝ≥0∞)⁻¹) *
        (∑ S ∈ s, oneStepDirichletOverlapLocalGradientFourth
          M n h p K j S omega hh) ∂M.P.toMeasure) =
        ((s.card : ℝ≥0∞)⁻¹) *
          ∑ S ∈ s, ∫⁻ omega,
            oneStepDirichletOverlapLocalGradientFourth
              M n h p K j S omega hh ∂M.P.toMeasure := by
      rw [lintegral_const_mul' _ _ (by finiteness), lintegral_finsetSum]
      intro S hS
      exact measurable_oneStepDirichletOverlapLocalGradientFourth
        M n h p K j S hh
    _ ≤ ((s.card : ℝ≥0∞)⁻¹) * ∑ _S ∈ s, B := by
      gcongr with S hS
      exact lintegral_oneStepDirichletOverlapLocalGradientFourth_le_uniform
        M n h p K j S hh hp hblock
    _ = B := by
      rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
        ENNReal.inv_mul_cancel hcard0 hcardTop, one_mul]
  
/-- Neumann counterpart of the normalized stationary-member sweep. -/
theorem lintegral_average_oneStepNeumannOverlapLocalGradientFourth_le_uniform
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (K : ℤ) (j : ℕ) (hh : 0 < h)
    (hp : vecNormSq p = 1) (hblock : (h : ℝ) ≤ M.delta⁻¹) :
    ∫⁻ omega,
        (((overlapCentersAtDepth (originCube d K) j).card : ℝ≥0∞)⁻¹) *
          (∑ S ∈ overlapCentersAtDepth (originCube d K) j,
            oneStepNeumannOverlapLocalGradientFourth
              M n h p K j S omega hh)
        ∂M.P.toMeasure ≤
      ENNReal.ofReal (oneStepSourceParentGradientConst ^ (4 : ℕ)) := by
  let s := overlapCentersAtDepth (originCube d K) j
  let B : ℝ≥0∞ := ENNReal.ofReal (oneStepSourceParentGradientConst ^ (4 : ℕ))
  have hs : s.Nonempty := overlapCentersAtDepth_nonempty _ _
  have hcard0 : (s.card : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hs.card_ne_zero
  have hcardTop : (s.card : ℝ≥0∞) ≠ ∞ := by finiteness
  calc
    (∫⁻ omega, ((s.card : ℝ≥0∞)⁻¹) *
        (∑ S ∈ s, oneStepNeumannOverlapLocalGradientFourth
          M n h p K j S omega hh) ∂M.P.toMeasure) =
        ((s.card : ℝ≥0∞)⁻¹) *
          ∑ S ∈ s, ∫⁻ omega,
            oneStepNeumannOverlapLocalGradientFourth
              M n h p K j S omega hh ∂M.P.toMeasure := by
      rw [lintegral_const_mul' _ _ (by finiteness), lintegral_finsetSum]
      intro S hS
      exact measurable_oneStepNeumannOverlapLocalGradientFourth
        M n h p K j S hh
    _ ≤ ((s.card : ℝ≥0∞)⁻¹) * ∑ _S ∈ s, B := by
      gcongr with S hS
      exact lintegral_oneStepNeumannOverlapLocalGradientFourth_le_uniform
        M n h p K j S hh hp hblock
    _ = B := by
      rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
        ENNReal.inv_mul_cancel hcard0 hcardTop, one_mul]

/-! ## Literal recentered remainder at every retained parent -/

/-- Coordinate-sum size of the actual Dirichlet harmonic remainder on a
retained overlap parent. -/
noncomputable def oneStepDirichletOverlapRemainderCoordinateSum
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (K : ℤ) (j : ℕ) (S : TriadicCube d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) : ℝ :=
  if hS : S ∈ overlapCentersAtDepth (originCube d K) j then
    ∑ k : Fin d,
      (eLpNorm (fun x ↦
          (oneStepDirichletAxisRemainder M n h omega p (cubeCenter S)
            K (S.scale + 1) (oneStepOverlapParent_subset_outerCube hS) hh).grad x k)
        2 (CubeCalderonZygmund.axisCubeNormalizedMeasure
          (oneStepCenteredAxisCorner (cubeCenter S) (S.scale + 1))
          (cubeScaleFactor (originCube d (S.scale + 1))))).toReal
  else 0

/-- Neumann counterpart of the literal recentered coordinate sum. -/
noncomputable def oneStepNeumannOverlapRemainderCoordinateSum
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (K : ℤ) (j : ℕ) (S : TriadicCube d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) : ℝ :=
  if hS : S ∈ overlapCentersAtDepth (originCube d K) j then
    ∑ k : Fin d,
      (eLpNorm (fun x ↦
          (oneStepNeumannAxisRemainder M n h omega p (cubeCenter S)
            K (S.scale + 1) (oneStepOverlapParent_subset_outerCube hS) hh).grad x k)
        2 (CubeCalderonZygmund.axisCubeNormalizedMeasure
          (oneStepCenteredAxisCorner (cubeCenter S) (S.scale + 1))
          (cubeScaleFactor (originCube d (S.scale + 1))))).toReal
  else 0

theorem oneStepDirichletOverlapRemainderCoordinateSum_nonneg
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (K : ℤ) (j : ℕ) (S : TriadicCube d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    0 ≤ oneStepDirichletOverlapRemainderCoordinateSum
      M n h p K j S omega hh := by
  unfold oneStepDirichletOverlapRemainderCoordinateSum
  split_ifs
  · exact Finset.sum_nonneg fun _ _ ↦ ENNReal.toReal_nonneg
  · exact le_rfl

theorem oneStepNeumannOverlapRemainderCoordinateSum_nonneg
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (K : ℤ) (j : ℕ) (S : TriadicCube d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    0 ≤ oneStepNeumannOverlapRemainderCoordinateSum
      M n h p K j S omega hh := by
  unfold oneStepNeumannOverlapRemainderCoordinateSum
  split_ifs
  · exact Finset.sum_nonneg fun _ _ ↦ ENNReal.toReal_nonneg
  · exact le_rfl

private theorem add_four_le_eight_sum_four_nested {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ (4 : ℕ) ≤ 8 * (a ^ (4 : ℕ) + b ^ (4 : ℕ)) := by
  have h := add_pow_le ha hb 4
  norm_num at h ⊢
  exact h

/-- Pointwise fourth-power domination of the literal Dirichlet recentered
remainder by the large restriction and its stationary local subtraction. -/
theorem ofReal_oneStepDirichletOverlapRemainderCoordinateSum_pow_four_le
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (K : ℤ) (j : ℕ) (S : TriadicCube d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    ENNReal.ofReal
        (oneStepDirichletOverlapRemainderCoordinateSum
          M n h p K j S omega hh ^ (4 : ℕ)) ≤
      ENNReal.ofReal (8 * (d : ℝ) ^ (4 : ℕ)) *
        ((oneStepDirichletOverlapLargeGradient
            M n h p K j S omega hh) ^ (4 : ℕ) +
          oneStepDirichletOverlapLocalGradientFourth
            M n h p K j S omega hh) := by
  by_cases hS : S ∈ overlapCentersAtDepth (originCube d K) j
  · let L : ℝ≥0∞ := oneStepDirichletOverlapLargeGradient
      M n h p K j S omega hh
    let b : ℝ := oneStepTranslatedDirichletNormalizedGradient
      M n h p (cubeCenter S) (S.scale + 1) omega hh
    have hside : 0 < cubeScaleFactor (originCube d (S.scale + 1)) := by
      simpa [cubeScaleFactor] using!
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) (S.scale + 1))
    have hLmem : MemLp
        (hilbertifyVecField
          (oneStepDirichletAxisLargeRestriction M n h omega p (cubeCenter S)
            K (S.scale + 1) (oneStepOverlapParent_subset_outerCube hS) hh).grad)
        2 (CubeCalderonZygmund.axisCubeNormalizedMeasure
          (oneStepCenteredAxisCorner (cubeCenter S) (S.scale + 1))
          (cubeScaleFactor (originCube d (S.scale + 1)))) :=
      CubeCalderonZygmund.memHilbertVectorL2_axisCubeNormalizedMeasure
        _ hside (memHilbertVectorL2_hilbertifyVecField
          (oneStepDirichletAxisLargeRestriction M n h omega p (cubeCenter S)
            K (S.scale + 1) (oneStepOverlapParent_subset_outerCube hS) hh).grad_memVectorL2)
    have hLtop : L ≠ ∞ := by
      simpa [L, oneStepDirichletOverlapLargeGradient, hS] using! hLmem.eLpNorm_ne_top
    have hb0 : 0 ≤ b := by
      unfold b oneStepTranslatedDirichletNormalizedGradient
      exact mul_nonneg
        (Real.rpow_nonneg
          (inv_nonneg.mpr (cubeVolume_nonneg (originCube d (S.scale + 1)))) _)
        (norm_nonneg _)
    have hcoord : oneStepDirichletOverlapRemainderCoordinateSum
        M n h p K j S omega hh ≤ (d : ℝ) * (L.toReal + b) := by
      simpa only [oneStepDirichletOverlapRemainderCoordinateSum, dite_eq_left hS,
        L, b, oneStepDirichletOverlapLargeGradient, dite_eq_left hS] using!
        oneStepDirichletAxisRemainder_coordinateSum_le_large_add_translated
          M n h omega p (cubeCenter S) K (S.scale + 1)
            (oneStepOverlapParent_subset_outerCube hS) hh
    have hR0 := oneStepDirichletOverlapRemainderCoordinateSum_nonneg
      M n h p K j S omega hh
    have hpow : oneStepDirichletOverlapRemainderCoordinateSum
        M n h p K j S omega hh ^ (4 : ℕ) ≤
          (8 * (d : ℝ) ^ (4 : ℕ)) *
            (L.toReal ^ (4 : ℕ) + b ^ (4 : ℕ)) := by
      calc
        _ ≤ ((d : ℝ) * (L.toReal + b)) ^ (4 : ℕ) :=
          pow_le_pow_left₀ hR0 hcoord 4
        _ = (d : ℝ) ^ (4 : ℕ) * (L.toReal + b) ^ (4 : ℕ) := by ring
        _ ≤ (d : ℝ) ^ (4 : ℕ) *
            (8 * (L.toReal ^ (4 : ℕ) + b ^ (4 : ℕ))) := by
          gcongr
          exact add_four_le_eight_sum_four_nested ENNReal.toReal_nonneg hb0
        _ = _ := by ring
    have hof := ENNReal.ofReal_le_ofReal hpow
    refine hof.trans_eq ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add
      (pow_nonneg ENNReal.toReal_nonneg 4) (pow_nonneg hb0 4),
      ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hLtop,
      ENNReal.ofReal_pow hb0]
    simp [oneStepDirichletOverlapLocalGradientFourth, hS,
      oneStepTranslatedDirichletNormalizedGradientFourth, L, b]
    rw [ENNReal.ofReal_pow hb0]
  · simp [oneStepDirichletOverlapRemainderCoordinateSum,
      oneStepDirichletOverlapLargeGradient,
      oneStepDirichletOverlapLocalGradientFourth, hS]

/-- Neumann version of the pointwise fourth-power recentering bound. -/
theorem ofReal_oneStepNeumannOverlapRemainderCoordinateSum_pow_four_le
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (K : ℤ) (j : ℕ) (S : TriadicCube d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    ENNReal.ofReal
        (oneStepNeumannOverlapRemainderCoordinateSum
          M n h p K j S omega hh ^ (4 : ℕ)) ≤
      ENNReal.ofReal (8 * (d : ℝ) ^ (4 : ℕ)) *
        ((oneStepNeumannOverlapLargeGradient
            M n h p K j S omega hh) ^ (4 : ℕ) +
          oneStepNeumannOverlapLocalGradientFourth
            M n h p K j S omega hh) := by
  by_cases hS : S ∈ overlapCentersAtDepth (originCube d K) j
  · let L : ℝ≥0∞ := oneStepNeumannOverlapLargeGradient
      M n h p K j S omega hh
    let b : ℝ := oneStepTranslatedNeumannNormalizedGradient
      M n h p (cubeCenter S) (S.scale + 1) omega hh
    have hside : 0 < cubeScaleFactor (originCube d (S.scale + 1)) := by
      simpa [cubeScaleFactor] using!
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) (S.scale + 1))
    have hLmem : MemLp
        (hilbertifyVecField
          (oneStepNeumannAxisLargeRestriction M n h omega p (cubeCenter S)
            K (S.scale + 1) (oneStepOverlapParent_subset_outerCube hS) hh).grad)
        2 (CubeCalderonZygmund.axisCubeNormalizedMeasure
          (oneStepCenteredAxisCorner (cubeCenter S) (S.scale + 1))
          (cubeScaleFactor (originCube d (S.scale + 1)))) :=
      CubeCalderonZygmund.memHilbertVectorL2_axisCubeNormalizedMeasure
        _ hside (memHilbertVectorL2_hilbertifyVecField
          (oneStepNeumannAxisLargeRestriction M n h omega p (cubeCenter S)
            K (S.scale + 1) (oneStepOverlapParent_subset_outerCube hS) hh).grad_memVectorL2)
    have hLtop : L ≠ ∞ := by
      simpa [L, oneStepNeumannOverlapLargeGradient, hS] using! hLmem.eLpNorm_ne_top
    have hb0 : 0 ≤ b := by
      unfold b oneStepTranslatedNeumannNormalizedGradient
      exact mul_nonneg
        (Real.rpow_nonneg
          (inv_nonneg.mpr (cubeVolume_nonneg (originCube d (S.scale + 1)))) _)
        (norm_nonneg _)
    have hcoord : oneStepNeumannOverlapRemainderCoordinateSum
        M n h p K j S omega hh ≤ (d : ℝ) * (L.toReal + b) := by
      simpa only [oneStepNeumannOverlapRemainderCoordinateSum, dite_eq_left hS,
        L, b, oneStepNeumannOverlapLargeGradient, dite_eq_left hS] using!
        oneStepNeumannAxisRemainder_coordinateSum_le_large_add_translated
          M n h omega p (cubeCenter S) K (S.scale + 1)
            (oneStepOverlapParent_subset_outerCube hS) hh
    have hR0 := oneStepNeumannOverlapRemainderCoordinateSum_nonneg
      M n h p K j S omega hh
    have hpow : oneStepNeumannOverlapRemainderCoordinateSum
        M n h p K j S omega hh ^ (4 : ℕ) ≤
          (8 * (d : ℝ) ^ (4 : ℕ)) *
            (L.toReal ^ (4 : ℕ) + b ^ (4 : ℕ)) := by
      calc
        _ ≤ ((d : ℝ) * (L.toReal + b)) ^ (4 : ℕ) :=
          pow_le_pow_left₀ hR0 hcoord 4
        _ = (d : ℝ) ^ (4 : ℕ) * (L.toReal + b) ^ (4 : ℕ) := by ring
        _ ≤ (d : ℝ) ^ (4 : ℕ) *
            (8 * (L.toReal ^ (4 : ℕ) + b ^ (4 : ℕ))) := by
          gcongr
          exact add_four_le_eight_sum_four_nested ENNReal.toReal_nonneg hb0
        _ = _ := by ring
    have hof := ENNReal.ofReal_le_ofReal hpow
    refine hof.trans_eq ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add
      (pow_nonneg ENNReal.toReal_nonneg 4) (pow_nonneg hb0 4),
      ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hLtop,
      ENNReal.ofReal_pow hb0]
    simp [oneStepNeumannOverlapLocalGradientFourth, hS,
      oneStepTranslatedNeumannNormalizedGradientFourth, L, b]
    rw [ENNReal.ofReal_pow hb0]
  · simp [oneStepNeumannOverlapRemainderCoordinateSum,
      oneStepNeumannOverlapLargeGradient,
      oneStepNeumannOverlapLocalGradientFourth, hS]

/-- A unit vector for the manuscript's Euclidean quadratic form has raw
`Pi` norm at most one. -/
theorem norm_le_one_of_vecNormSq_eq_one {d : ℕ} {p : Vec d}
    (hp : vecNormSq p = 1) : ‖p‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
  intro i
  have hi : p i ^ 2 ≤ vecNormSq p := by
    unfold vecNormSq vecDot
    simpa [pow_two] using!
      (Finset.single_le_sum (fun j _hj => sq_nonneg (p j)) (Finset.mem_univ i))
  rw [hp] at hi
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith [sq_nonneg (p i - 1), sq_nonneg (p i + 1)]

/-- The raw-vector endpoint in CoarseGraining is stated using the `Pi` norm.
This wrapper records the finite-dimensional conversion to the Hilbert norm
used by the overlap sweep. -/
theorem eLpNorm_hilbertifyVecField_le_dimension_mul
    {d : ℕ} {p : ℝ≥0∞} {Q : TriadicCube d} (F : Vec d → Vec d) :
    SubdiffusiveProcess.RawLp.eLpNorm (hilbertifyVecField F) p (normalizedCubeMeasure Q) ≤
      ENNReal.ofReal (d : ℝ) * SubdiffusiveProcess.RawLp.eLpNorm F p (normalizedCubeMeasure Q) := by
  have hb : ∀ᵐ x ∂normalizedCubeMeasure Q,
      ‖hilbertifyVecField F x‖₊ ≤ (d : ℝ≥0) * ‖F x‖₊ :=
    Filter.Eventually.of_forall fun x => by
      exact_mod_cast HilbertVec.norm_ofVec_le_mul_norm (F x)
  by_cases hp0 : p = 0
  · simp [SubdiffusiveProcess.RawLp.eLpNorm, hp0]
  by_cases hpt : p = ∞
  · simpa only [SubdiffusiveProcess.RawLp.eLpNorm, hpt, ite_eq_right (by norm_num : (∞ : ℝ≥0∞) ≠ 0),
      ite_true, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_natCast, ENNReal.ofReal_natCast] using
      eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul hb
  · simpa only [SubdiffusiveProcess.RawLp.eLpNorm, ite_eq_right hp0, ite_eq_right hpt,
      ENNReal.smul_def, smul_eq_mul, ENNReal.coe_natCast, ENNReal.ofReal_natCast] using
      eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul hb (ENNReal.toReal_pos hp0 hpt)

/-- The measurable vector comparison in the guarded norm API. -/
theorem eLpNorm_hilbertifyVecField_le_dimension_mul_of_aestronglyMeasurable
    {d : ℕ} {p : ℝ≥0∞} {Q : TriadicCube d} (F : Vec d → Vec d)
    (hF : AEStronglyMeasurable F (normalizedCubeMeasure Q)) :
    eLpNorm (hilbertifyVecField F) p (normalizedCubeMeasure Q) ≤
      ENNReal.ofReal (d : ℝ) * eLpNorm F p (normalizedCubeMeasure Q) := by
  have hh : AEStronglyMeasurable (hilbertifyVecField F) (normalizedCubeMeasure Q) := by
    simpa only [hilbertifyVecField] using!
      (HilbertVec.continuousLinearEquivVec d).symm.continuous.comp_aestronglyMeasurable hF
  simpa only [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hh, SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hF] using
    eLpNorm_hilbertifyVecField_le_dimension_mul (p := p) (Q := Q) F

/-- The literal shell forcing in a unit direction is pointwise no larger
than its scalar multiplier in the raw-vector norm. -/
private theorem eLpNorm_oneStepShellForcing_le_multiplier
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p : Vec d) (Q : TriadicCube d)
    (hh : 0 < h) (hp : vecNormSq p = 1) :
    eLpNorm
        (oneStepShellForcingW14 M n h omega p Q hh).toField 4
        (normalizedCubeMeasure Q) ≤
      eLpNorm (fun x ↦ oneStepMultiplierAt M n h x omega) 4
        (normalizedCubeMeasure Q) := by
  have hm : AEStronglyMeasurable
      (oneStepShellForcingW14 M n h omega p Q hh).toField (normalizedCubeMeasure Q) := by
    simpa only [oneStepShellForcingW14_toField_apply] using!
      ((continuous_oneStepMultiplierAt_sample M n h omega).smul
        (continuous_const : Continuous fun _ : Vec d => p)).aestronglyMeasurable
  apply eLpNorm_mono_ae hm
  filter_upwards [] with x
  rw [oneStepShellForcingW14_toField_apply]
  calc
    ‖oneStepMultiplierAt M n h x omega • p‖ =
        |oneStepMultiplierAt M n h x omega| * ‖p‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |oneStepMultiplierAt M n h x omega| * 1 :=
      mul_le_mul_of_nonneg_left (norm_le_one_of_vecNormSq_eq_one hp) (abs_nonneg _)
    _ = ‖oneStepMultiplierAt M n h x omega‖ := by
      rw [mul_one, Real.norm_eq_abs]

/-- Fourth-integrability of the scalar shell multiplier on any origin cube. -/
private theorem memLp_four_oneStepMultiplier_spatial
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    MemLp (fun x ↦ oneStepMultiplierAt M n h x omega) 4
      (normalizedCubeMeasure (originCube d m)) := by
  have hcont := (oneStepMultiplierContinuousMap M n h omega).continuous
  have hmem := SubdiffusiveProcess.CoarseGrainingVocab.memLp_normalizedCubeMeasure_of_continuous
    (originCube d m) (4 : ℝ≥0∞) hcont
  convert hmem using 1
  funext x
  rw [oneStepMultiplierContinuousMap_apply M n h omega x hh]

/-- Measurability of a parameter-dependent spatial `L⁴` norm. -/
theorem measurable_eLpNorm_four_prod_right
    {Omega X : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
    (nu : Measure X) [SFinite nu] (f : Omega → X → ℝ)
    (hf : Measurable (Function.uncurry f)) :
    Measurable fun omega => eLpNorm (f omega) 4 nu := by
  rw [show (fun omega => eLpNorm (f omega) 4 nu) =
      fun omega =>
        (∫⁻ x, ‖f omega x‖ₑ ^ (4 : ℝ) ∂nu) ^ (1 / 4 : ℝ) by
    funext omega
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) (hf.of_uncurry_left.aestronglyMeasurable)]
    norm_num]
  have hjoint : Measurable (Function.uncurry fun omega x =>
      ‖f omega x‖ₑ ^ (4 : ℝ)) := by
    simpa only [Function.uncurry_apply_pair] using! hf.enorm.pow_const (4 : ℝ)
  exact ENNReal.continuous_rpow_const.measurable.comp hjoint.lintegral_prod_right

/-- Dirichlet Calderon--Zygmund control of the actual large-cube solution in
the Hilbert `L⁴` setting needed by the overlap sweep. -/
theorem exists_oneStepOriginDirichlet_gradient_four_cz (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p : Vec d) (m : ℤ) (hh : 0 < h)
        (_hp : vecNormSq p = 1),
        MemLp
            (hilbertifyVecField
              (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function.grad)
            4 (normalizedCubeMeasure (originCube d m)) ∧
          eLpNorm
              (hilbertifyVecField
                (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function.grad)
              4 (normalizedCubeMeasure (originCube d m)) ≤
            C * eLpNorm (fun x ↦ oneStepMultiplierAt M n h x omega) 4
              (normalizedCubeMeasure (originCube d m)) := by
  obtain ⟨C, hCpos, hCZ⟩ :=
    CubeCalderonZygmund.exists_cubeDirichletDivergence_cz
      d oneStepFourExponent
  let C4 : ℝ≥0∞ := ENNReal.ofReal ((d : ℝ) * C)
  refine ⟨C4, ?_, ?_⟩
  · exact ENNReal.ofReal_lt_top
  · intro M n h omega p m hh hp
    let Q := originCube d m
    let G := oneStepShellForcingW14 M n h omega p Q hh
    let u := oneStepOriginDirichletSolution M n h p m omega hh
    have hGhilbert : MemLp (fun x ↦ HilbertVec.ofVec (G.toField x)) 4
        (normalizedCubeMeasure Q) := by
      simpa only [oneStepFourExponent_exponent] using! G.euclideanMemLp
    have hGraw : MemLp G.toField 4 (normalizedCubeMeasure Q) := by
      simpa only [Function.comp_apply,
        HilbertVec.continuousLinearEquivVec_apply, HilbertVec.toVec_ofVec] using!
        (HilbertVec.continuousLinearEquivVec d).toContinuousLinearMap.comp_memLp'
          hGhilbert
    have huweak : IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d ↦ (1 : Mat d)) (openCubeSet Q) u
        (fun x ↦ -G.toField x) := by
      have ha : identityCoeffField d = (fun _ : Vec d ↦ (1 : Mat d)) := by
        funext x i j
        simp [identityCoeffField, scalarMatrix, Matrix.one_apply]
      rw [← ha]
      simpa only [Q, G, u, oneStepShellForcingW14_toField_apply,
        neg_smul] using!
        oneStepOriginDirichletSolution_isWeakSolution M n h p m omega hh
    obtain ⟨hgradRaw, hgradBound⟩ :=
      hCZ Q G.toField hGraw u huweak
    have hgradHilbert : MemLp
        (hilbertifyVecField u.toH1Function.grad) 4
        (normalizedCubeMeasure Q) := by
      simpa only [hilbertifyVecField, Function.comp_apply,
        HilbertVec.ofVecL_apply] using!
        (HilbertVec.ofVecL d).comp_memLp' hgradRaw
    refine ⟨by simpa only [Q, u] using! hgradHilbert, ?_⟩
    have hscalar := memLp_four_oneStepMultiplier_spatial M n h m omega hh
    have hforcing := eLpNorm_oneStepShellForcing_le_multiplier
      M n h omega p Q hh hp
    have hrawENN :
        eLpNorm u.toH1Function.grad 4 (normalizedCubeMeasure Q) ≤
          ENNReal.ofReal C * eLpNorm G.toField 4 (normalizedCubeMeasure Q) := by
      apply (ENNReal.toReal_le_toReal hgradRaw.eLpNorm_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGraw.eLpNorm_ne_top)).mp
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCpos.le]
      simpa only [cubeLpNorm, Q, G, u, oneStepFourExponent_exponent] using! hgradBound
    calc
      eLpNorm (hilbertifyVecField u.toH1Function.grad) 4
          (normalizedCubeMeasure Q) ≤
        ENNReal.ofReal (d : ℝ) *
          eLpNorm u.toH1Function.grad 4 (normalizedCubeMeasure Q) :=
        eLpNorm_hilbertifyVecField_le_dimension_mul_of_aestronglyMeasurable u.toH1Function.grad
          (memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet Q
            u.toH1Function.grad_memVectorL2).aestronglyMeasurable
      _ ≤ ENNReal.ofReal (d : ℝ) *
          (ENNReal.ofReal C * eLpNorm G.toField 4
            (normalizedCubeMeasure Q)) := by
        gcongr
      _ = C4 * eLpNorm G.toField 4 (normalizedCubeMeasure Q) := by
        dsimp only [C4]
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg d)]
        ac_rfl
      _ ≤ C4 * eLpNorm (fun x ↦ oneStepMultiplierAt M n h x omega) 4
          (normalizedCubeMeasure Q) := by
        change eLpNorm G.toField 4 (normalizedCubeMeasure Q) ≤
          eLpNorm (fun x ↦ oneStepMultiplierAt M n h x omega) 4
            (normalizedCubeMeasure Q) at hforcing
        gcongr

/-- Neumann counterpart of the actual large-cube `L⁴` gradient estimate. -/
theorem exists_oneStepOriginNeumann_gradient_four_cz (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p : Vec d) (m : ℤ) (hh : 0 < h)
        (_hp : vecNormSq p = 1),
        MemLp
            (hilbertifyVecField
              (oneStepOriginNeumannSolution M n h p m omega hh).toH1Function.grad)
            4 (normalizedCubeMeasure (originCube d m)) ∧
          eLpNorm
              (hilbertifyVecField
                (oneStepOriginNeumannSolution M n h p m omega hh).toH1Function.grad)
              4 (normalizedCubeMeasure (originCube d m)) ≤
            C * eLpNorm (fun x ↦ oneStepMultiplierAt M n h x omega) 4
              (normalizedCubeMeasure (originCube d m)) := by
  obtain ⟨C, hCpos, hCZ⟩ := exists_oneStepShell_neumannDivergence_cz d
  let C4 : ℝ≥0∞ := ENNReal.ofReal ((d : ℝ) * C)
  refine ⟨C4, ENNReal.ofReal_lt_top, ?_⟩
  intro M n h omega p m hh hp
  let Q := originCube d m
  let G := oneStepShellForcingW14 M n h omega p Q hh
  let u := oneStepOriginNeumannSolution M n h p m omega hh
  have huweak : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d ↦ (1 : Mat d)) (openCubeSet Q) u
      (fun x ↦ -G.toField x) := by
    have ha : identityCoeffField d = (fun _ : Vec d ↦ (1 : Mat d)) := by
      funext x i j
      simp [identityCoeffField, scalarMatrix, Matrix.one_apply]
    rw [← ha]
    simpa only [Q, G, u, oneStepShellForcingW14_toField_apply,
      neg_smul] using!
      oneStepOriginNeumannSolution_isWeakSolution M n h p m omega hh
  obtain ⟨hgradRaw, hgradBound⟩ := hCZ M n h omega p Q hh u huweak
  have hgradHilbert : MemLp
      (hilbertifyVecField u.toH1Function.grad) 4
      (normalizedCubeMeasure Q) := by
    simpa only [hilbertifyVecField, Function.comp_apply,
      HilbertVec.ofVecL_apply] using!
      (HilbertVec.ofVecL d).comp_memLp' hgradRaw
  refine ⟨by simpa only [Q, u] using! hgradHilbert, ?_⟩
  have hGhilbert : MemLp (fun x ↦ HilbertVec.ofVec (G.toField x)) 4
      (normalizedCubeMeasure Q) := by
    simpa only [oneStepFourExponent_exponent] using! G.euclideanMemLp
  have hGraw : MemLp G.toField 4 (normalizedCubeMeasure Q) := by
    simpa only [Function.comp_apply,
      HilbertVec.continuousLinearEquivVec_apply, HilbertVec.toVec_ofVec] using!
      (HilbertVec.continuousLinearEquivVec d).toContinuousLinearMap.comp_memLp'
        hGhilbert
  have hforcing := eLpNorm_oneStepShellForcing_le_multiplier
    M n h omega p Q hh hp
  have hrawENN :
      eLpNorm u.toH1Function.grad 4 (normalizedCubeMeasure Q) ≤
        ENNReal.ofReal C * eLpNorm G.toField 4 (normalizedCubeMeasure Q) := by
    apply (ENNReal.toReal_le_toReal hgradRaw.eLpNorm_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGraw.eLpNorm_ne_top)).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCpos.le]
    simpa only [cubeLpNorm, Q, G, u] using! hgradBound
  calc
    eLpNorm (hilbertifyVecField u.toH1Function.grad) 4
        (normalizedCubeMeasure Q) ≤
      ENNReal.ofReal (d : ℝ) *
        eLpNorm u.toH1Function.grad 4 (normalizedCubeMeasure Q) :=
      eLpNorm_hilbertifyVecField_le_dimension_mul_of_aestronglyMeasurable u.toH1Function.grad
          (memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet Q
            u.toH1Function.grad_memVectorL2).aestronglyMeasurable
    _ ≤ ENNReal.ofReal (d : ℝ) *
        (ENNReal.ofReal C * eLpNorm G.toField 4
          (normalizedCubeMeasure Q)) := by
      gcongr
    _ = C4 * eLpNorm G.toField 4 (normalizedCubeMeasure Q) := by
      dsimp only [C4]
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg d)]
      ac_rfl
    _ ≤ C4 * eLpNorm (fun x ↦ oneStepMultiplierAt M n h x omega) 4
        (normalizedCubeMeasure Q) := by
      change eLpNorm G.toField 4 (normalizedCubeMeasure Q) ≤
        eLpNorm (fun x ↦ oneStepMultiplierAt M n h x omega) 4
          (normalizedCubeMeasure Q) at hforcing
      gcongr

/-- Uniform mixed fourth moment of the global Dirichlet `L⁴` gradient. -/
theorem exists_lintegral_oneStepOriginDirichlet_gradient_four_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (m : ℤ) (hh : 0 < h) (_hp : vecNormSq p = 1),
        ∫⁻ omega,
            (eLpNorm
              (hilbertifyVecField
                (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function.grad)
              4 (normalizedCubeMeasure (originCube d m))) ^ (4 : ℝ)
            ∂M.P.toMeasure ≤
          C * (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) := by
  obtain ⟨C, hCtop, hCZ⟩ := exists_oneStepOriginDirichlet_gradient_four_cz d
  refine ⟨C ^ (4 : ℝ),
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hCtop.ne, ?_⟩
  intro M n h p m hh hp
  let nu := normalizedCubeMeasure (originCube d m)
  let F : _root_.SubdiffusiveProcess.Model.PotentialSample d → Vec d → ℝ := fun omega x ↦
    oneStepMultiplierAt M n h x omega
  have hFmeas : Measurable (Function.uncurry F) := by
    simpa only [F] using! measurable_oneStepMultiplierAt_uncurry M n h
  have hnormMeas : Measurable fun omega => eLpNorm (F omega) 4 nu :=
    measurable_eLpNorm_four_prod_right nu F hFmeas
  have hmult :
      (∫⁻ omega, (eLpNorm (F omega) 4 nu) ^ (4 : ℝ) ∂M.P.toMeasure) ≤
        (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) := by
    calc
      (∫⁻ omega, (eLpNorm (F omega) 4 nu) ^ (4 : ℝ) ∂M.P.toMeasure) =
          ∫⁻ omega, ∫⁻ x, ‖F omega x‖ₑ ^ (4 : ℝ) ∂nu ∂M.P.toMeasure := by
        apply lintegral_congr
        intro omega
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) (by simpa only [Function.comp_def, Function.uncurry_apply_pair] using!
          (hFmeas.comp ((measurable_const (a := omega)).prodMk measurable_id)).aestronglyMeasurable)]
        norm_num only [ENNReal.toReal_ofNat]
        have hquarter : (1 / 4 : ℝ) = (4 : ℝ)⁻¹ := by norm_num
        rw [hquarter, ENNReal.rpow_inv_rpow (by norm_num : (4 : ℝ) ≠ 0)]
      _ ≤ (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) := by
        simpa only [F, nu] using!
          lintegral_lintegral_oneStepMultiplier_four_le M n h m hh
  calc
    (∫⁻ omega,
        (eLpNorm
          (hilbertifyVecField
            (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function.grad)
          4 nu) ^ (4 : ℝ) ∂M.P.toMeasure) ≤
      ∫⁻ omega, (C * eLpNorm (F omega) 4 nu) ^ (4 : ℝ) ∂M.P.toMeasure := by
        apply lintegral_mono
        intro omega
        exact ENNReal.rpow_le_rpow (hCZ M n h omega p m hh hp).2 (by norm_num)
    _ = ∫⁻ omega, C ^ (4 : ℝ) *
        (eLpNorm (F omega) 4 nu) ^ (4 : ℝ) ∂M.P.toMeasure := by
      apply lintegral_congr
      intro omega
      exact ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ = C ^ (4 : ℝ) *
        ∫⁻ omega, (eLpNorm (F omega) 4 nu) ^ (4 : ℝ) ∂M.P.toMeasure := by
      rw [lintegral_const_mul'' _ (hnormMeas.pow_const (4 : ℝ)).aemeasurable]
    _ ≤ C ^ (4 : ℝ) *
        (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) := by
      gcongr

/-- Uniform mixed fourth moment of the global Neumann `L⁴` gradient. -/
theorem exists_lintegral_oneStepOriginNeumann_gradient_four_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (m : ℤ) (hh : 0 < h) (_hp : vecNormSq p = 1),
        ∫⁻ omega,
            (eLpNorm
              (hilbertifyVecField
                (oneStepOriginNeumannSolution M n h p m omega hh).toH1Function.grad)
              4 (normalizedCubeMeasure (originCube d m))) ^ (4 : ℝ)
            ∂M.P.toMeasure ≤
          C * (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) := by
  obtain ⟨C, hCtop, hCZ⟩ := exists_oneStepOriginNeumann_gradient_four_cz d
  refine ⟨C ^ (4 : ℝ),
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hCtop.ne, ?_⟩
  intro M n h p m hh hp
  let nu := normalizedCubeMeasure (originCube d m)
  let F : _root_.SubdiffusiveProcess.Model.PotentialSample d → Vec d → ℝ := fun omega x ↦
    oneStepMultiplierAt M n h x omega
  have hFmeas : Measurable (Function.uncurry F) := by
    simpa only [F] using! measurable_oneStepMultiplierAt_uncurry M n h
  have hnormMeas : Measurable fun omega => eLpNorm (F omega) 4 nu :=
    measurable_eLpNorm_four_prod_right nu F hFmeas
  have hmult :
      (∫⁻ omega, (eLpNorm (F omega) 4 nu) ^ (4 : ℝ) ∂M.P.toMeasure) ≤
        (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) := by
    calc
      (∫⁻ omega, (eLpNorm (F omega) 4 nu) ^ (4 : ℝ) ∂M.P.toMeasure) =
          ∫⁻ omega, ∫⁻ x, ‖F omega x‖ₑ ^ (4 : ℝ) ∂nu ∂M.P.toMeasure := by
        apply lintegral_congr
        intro omega
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) (by simpa only [Function.comp_def, Function.uncurry_apply_pair] using!
          (hFmeas.comp ((measurable_const (a := omega)).prodMk measurable_id)).aestronglyMeasurable)]
        norm_num only [ENNReal.toReal_ofNat]
        have hquarter : (1 / 4 : ℝ) = (4 : ℝ)⁻¹ := by norm_num
        rw [hquarter, ENNReal.rpow_inv_rpow (by norm_num : (4 : ℝ) ≠ 0)]
      _ ≤ (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) := by
        simpa only [F, nu] using!
          lintegral_lintegral_oneStepMultiplier_four_le M n h m hh
  calc
    (∫⁻ omega,
        (eLpNorm
          (hilbertifyVecField
            (oneStepOriginNeumannSolution M n h p m omega hh).toH1Function.grad)
          4 nu) ^ (4 : ℝ) ∂M.P.toMeasure) ≤
      ∫⁻ omega, (C * eLpNorm (F omega) 4 nu) ^ (4 : ℝ) ∂M.P.toMeasure := by
        apply lintegral_mono
        intro omega
        exact ENNReal.rpow_le_rpow (hCZ M n h omega p m hh hp).2 (by norm_num)
    _ = ∫⁻ omega, C ^ (4 : ℝ) *
        (eLpNorm (F omega) 4 nu) ^ (4 : ℝ) ∂M.P.toMeasure := by
      apply lintegral_congr
      intro omega
      exact ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ = C ^ (4 : ℝ) *
        ∫⁻ omega, (eLpNorm (F omega) 4 nu) ^ (4 : ℝ) ∂M.P.toMeasure := by
      rw [lintegral_const_mul'' _ (hnormMeas.pow_const (4 : ℝ)).aemeasurable]
    _ ≤ C ^ (4 : ℝ) *
        (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) := by
      gcongr

/-- The normalized finite-overlap average of local `L²` fourth powers is
controlled by the normalized parent `L⁴` mass. -/
theorem overlapCentersAtDepth_average_eLpNorm_two_rpow_four_le
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (f : Vec d → HilbertVec d)
    (hf : MemLp f 4 (normalizedCubeMeasure Q)) :
    (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹) *
        (∑ S ∈ overlapCentersAtDepth Q j,
          (eLpNorm f 2 (normalizedOverlapCubeMeasure S)) ^ (4 : ℝ)) ≤
      (3 ^ d : ℝ≥0∞) *
        (eLpNorm f 4 (normalizedCubeMeasure Q)) ^ (4 : ℝ) := by
  have hlocal : ∀ S ∈ overlapCentersAtDepth Q j,
      (eLpNorm f 2 (normalizedOverlapCubeMeasure S)) ^ (4 : ℝ) ≤
        ∫⁻ x, ‖f x‖ₑ ^ (4 : ℝ) ∂normalizedOverlapCubeMeasure S := by
    intro S hS
    have hfS : MemLp f 4 (normalizedOverlapCubeMeasure S) :=
      memLp_normalizedOverlapCubeMeasure_of_memLp_normalizedCubeMeasure hS hf
    let : IsProbabilityMeasure (normalizedOverlapCubeMeasure S) :=
      ⟨normalizedOverlapCubeMeasure_apply_univ S⟩
    have hnorm : eLpNorm f 2 (normalizedOverlapCubeMeasure S) ≤
        eLpNorm f 4 (normalizedOverlapCubeMeasure S) :=
      eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (2 : ℝ≥0∞) ≤ 4)
    calc
      (eLpNorm f 2 (normalizedOverlapCubeMeasure S)) ^ (4 : ℝ) ≤
          (eLpNorm f 4 (normalizedOverlapCubeMeasure S)) ^ (4 : ℝ) :=
        ENNReal.rpow_le_rpow hnorm (by norm_num)
      _ = ∫⁻ x, ‖f x‖ₑ ^ (4 : ℝ) ∂normalizedOverlapCubeMeasure S := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hfS.aestronglyMeasurable]
        norm_num only [ENNReal.toReal_ofNat]
        have hquarter : (1 / 4 : ℝ) = (4 : ℝ)⁻¹ := by norm_num
        rw [hquarter, ENNReal.rpow_inv_rpow (by norm_num : (4 : ℝ) ≠ 0)]
  calc
    (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹) *
        (∑ S ∈ overlapCentersAtDepth Q j,
          (eLpNorm f 2 (normalizedOverlapCubeMeasure S)) ^ (4 : ℝ)) ≤
      (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹) *
        (∑ S ∈ overlapCentersAtDepth Q j,
          ∫⁻ x, ‖f x‖ₑ ^ (4 : ℝ) ∂normalizedOverlapCubeMeasure S) := by
      gcongr with S hS
      exact hlocal S hS
    _ ≤ (3 ^ d : ℝ≥0∞) *
        ∫⁻ x, ‖f x‖ₑ ^ (4 : ℝ) ∂normalizedCubeMeasure Q := by
      apply overlapCentersAtDepth_average_lintegral_normalizedOverlapCubeMeasure_le
      · simpa [cubeMeasure] using!
          (memLp_cubeMeasure_of_memLp_normalizedCubeMeasure Q hf).aestronglyMeasurable.enorm.pow_const
            (4 : ℝ)
      · intro S hS
        simpa [overlapCubeMeasure] using!
          (memLp_overlapCubeMeasure_of_memLp_normalizedOverlapCubeMeasure S
            (memLp_normalizedOverlapCubeMeasure_of_memLp_normalizedCubeMeasure
              hS hf)).aestronglyMeasurable.enorm.pow_const (4 : ℝ)
    _ = (3 ^ d : ℝ≥0∞) *
        (eLpNorm f 4 (normalizedCubeMeasure Q)) ^ (4 : ℝ) := by
      congr 1
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
      norm_num only [ENNReal.toReal_ofNat]
      have hquarter : (1 / 4 : ℝ) = (4 : ℝ)⁻¹ := by norm_num
      rw [hquarter, ENNReal.rpow_inv_rpow (by norm_num : (4 : ℝ) ≠ 0)]

/-- The full Dirichlet large-solution overlap sweep, integrated over the
random law.  The bound is uniform in the outer scale and overlap depth. -/
theorem exists_lintegral_oneStepOriginDirichlet_overlapGradient_four_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (K : ℤ) (j : ℕ) (hh : 0 < h)
        (_hp : vecNormSq p = 1),
        ∫⁻ omega,
            (((overlapCentersAtDepth (originCube d K) j).card : ℝ≥0∞)⁻¹) *
              (∑ S ∈ overlapCentersAtDepth (originCube d K) j,
                (eLpNorm
                  (hilbertifyVecField
                    (oneStepOriginDirichletSolution
                      M n h p K omega hh).toH1Function.grad)
                  2 (normalizedOverlapCubeMeasure S)) ^ (4 : ℝ))
            ∂M.P.toMeasure ≤
          C * (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) := by
  obtain ⟨C, hCtop, hglobal⟩ :=
    exists_lintegral_oneStepOriginDirichlet_gradient_four_le d
  obtain ⟨Ccz, _hCczTop, hCZ⟩ :=
    exists_oneStepOriginDirichlet_gradient_four_cz d
  refine ⟨(3 ^ d : ℝ≥0∞) * C,
    ENNReal.mul_lt_top (by finiteness) hCtop, ?_⟩
  intro M n h p K j hh hp
  let Q := originCube d K
  let G : _root_.SubdiffusiveProcess.Model.PotentialSample d → Vec d → HilbertVec d := fun omega ↦
    hilbertifyVecField
      (oneStepOriginDirichletSolution M n h p K omega hh).toH1Function.grad
  calc
    (∫⁻ omega,
        (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹) *
          (∑ S ∈ overlapCentersAtDepth Q j,
            (eLpNorm (G omega) 2
              (normalizedOverlapCubeMeasure S)) ^ (4 : ℝ))
        ∂M.P.toMeasure) ≤
      ∫⁻ omega, (3 ^ d : ℝ≥0∞) *
        (eLpNorm (G omega) 4 (normalizedCubeMeasure Q)) ^ (4 : ℝ)
        ∂M.P.toMeasure := by
      apply lintegral_mono
      intro omega
      exact overlapCentersAtDepth_average_eLpNorm_two_rpow_four_le Q j
        (G omega) (by simpa only [G, Q] using! (hCZ M n h omega p K hh hp).1)
    _ = (3 ^ d : ℝ≥0∞) *
        ∫⁻ omega, (eLpNorm (G omega) 4
          (normalizedCubeMeasure Q)) ^ (4 : ℝ) ∂M.P.toMeasure :=
      lintegral_const_mul' _ _ (by finiteness)
    _ ≤ (3 ^ d : ℝ≥0∞) *
        (C * (ENNReal.ofReal
          (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ)) := by
      gcongr
      simpa only [G, Q] using! hglobal M n h p K hh hp
    _ = ((3 ^ d : ℝ≥0∞) * C) *
        (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) := by
      ac_rfl

/-- Neumann counterpart of the integrated finite-overlap sweep. -/
theorem exists_lintegral_oneStepOriginNeumann_overlapGradient_four_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (K : ℤ) (j : ℕ) (hh : 0 < h)
        (_hp : vecNormSq p = 1),
        ∫⁻ omega,
            (((overlapCentersAtDepth (originCube d K) j).card : ℝ≥0∞)⁻¹) *
              (∑ S ∈ overlapCentersAtDepth (originCube d K) j,
                (eLpNorm
                  (hilbertifyVecField
                    (oneStepOriginNeumannSolution
                      M n h p K omega hh).toH1Function.grad)
                  2 (normalizedOverlapCubeMeasure S)) ^ (4 : ℝ))
            ∂M.P.toMeasure ≤
          C * (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) := by
  obtain ⟨C, hCtop, hglobal⟩ :=
    exists_lintegral_oneStepOriginNeumann_gradient_four_le d
  obtain ⟨Ccz, _hCczTop, hCZ⟩ :=
    exists_oneStepOriginNeumann_gradient_four_cz d
  refine ⟨(3 ^ d : ℝ≥0∞) * C,
    ENNReal.mul_lt_top (by finiteness) hCtop, ?_⟩
  intro M n h p K j hh hp
  let Q := originCube d K
  let G : _root_.SubdiffusiveProcess.Model.PotentialSample d → Vec d → HilbertVec d := fun omega ↦
    hilbertifyVecField
      (oneStepOriginNeumannSolution M n h p K omega hh).toH1Function.grad
  calc
    (∫⁻ omega,
        (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹) *
          (∑ S ∈ overlapCentersAtDepth Q j,
            (eLpNorm (G omega) 2
              (normalizedOverlapCubeMeasure S)) ^ (4 : ℝ))
        ∂M.P.toMeasure) ≤
      ∫⁻ omega, (3 ^ d : ℝ≥0∞) *
        (eLpNorm (G omega) 4 (normalizedCubeMeasure Q)) ^ (4 : ℝ)
        ∂M.P.toMeasure := by
      apply lintegral_mono
      intro omega
      exact overlapCentersAtDepth_average_eLpNorm_two_rpow_four_le Q j
        (G omega) (by simpa only [G, Q] using! (hCZ M n h omega p K hh hp).1)
    _ = (3 ^ d : ℝ≥0∞) *
        ∫⁻ omega, (eLpNorm (G omega) 4
          (normalizedCubeMeasure Q)) ^ (4 : ℝ) ∂M.P.toMeasure :=
      lintegral_const_mul' _ _ (by finiteness)
    _ ≤ (3 ^ d : ℝ≥0∞) *
        (C * (ENNReal.ofReal
          (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ)) := by
      gcongr
      simpa only [G, Q] using! hglobal M n h p K hh hp
    _ = ((3 ^ d : ℝ≥0∞) * C) *
        (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) := by
      ac_rfl

/-- Integrated Dirichlet sweep in the literal axis-restriction observable
consumed by the nested harmonic estimate. -/
theorem exists_lintegral_oneStepDirichletOverlapLargeGradient_four_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (K : ℤ) (j : ℕ) (hh : 0 < h)
        (_hp : vecNormSq p = 1),
        ∫⁻ omega,
            (((overlapCentersAtDepth (originCube d K) j).card : ℝ≥0∞)⁻¹) *
              (∑ S ∈ overlapCentersAtDepth (originCube d K) j,
                (oneStepDirichletOverlapLargeGradient
                  M n h p K j S omega hh) ^ (4 : ℝ))
            ∂M.P.toMeasure ≤
          C * (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) := by
  obtain ⟨C, hCtop, hbound⟩ :=
    exists_lintegral_oneStepOriginDirichlet_overlapGradient_four_le d
  refine ⟨C, hCtop, ?_⟩
  intro M n h p K j hh hp
  convert hbound M n h p K j hh hp using 1
  apply lintegral_congr
  intro omega
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  rw [oneStepDirichletOverlapLargeGradient_eq M n h p K j S omega hh hS]

/-- Integrated Neumann sweep in the literal axis-restriction observable. -/
theorem exists_lintegral_oneStepNeumannOverlapLargeGradient_four_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (K : ℤ) (j : ℕ) (hh : 0 < h)
        (_hp : vecNormSq p = 1),
        ∫⁻ omega,
            (((overlapCentersAtDepth (originCube d K) j).card : ℝ≥0∞)⁻¹) *
              (∑ S ∈ overlapCentersAtDepth (originCube d K) j,
                (oneStepNeumannOverlapLargeGradient
                  M n h p K j S omega hh) ^ (4 : ℝ))
            ∂M.P.toMeasure ≤
          C * (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) := by
  obtain ⟨C, hCtop, hbound⟩ :=
    exists_lintegral_oneStepOriginNeumann_overlapGradient_four_le d
  refine ⟨C, hCtop, ?_⟩
  intro M n h p K j hh hp
  convert hbound M n h p K j hh hp using 1
  apply lintegral_congr
  intro omega
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  rw [oneStepNeumannOverlapLargeGradient_eq M n h p K j S omega hh hS]

/-! ## Integrated nested-remainder sweep -/

/-- Uniform fourth-moment sweep for the literal Dirichlet recentered
remainders.  It is uniform in the outer scale and in every nesting depth. -/
theorem exists_lintegral_oneStepDirichletOverlapRemainderCoordinateSum_four_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (K : ℤ) (j : ℕ) (hh : 0 < h)
        (_hp : vecNormSq p = 1) (_hblock : (h : ℝ) ≤ M.delta⁻¹),
        ∫⁻ omega,
            (((overlapCentersAtDepth (originCube d K) j).card : ℝ≥0∞)⁻¹) *
              (∑ S ∈ overlapCentersAtDepth (originCube d K) j,
                ENNReal.ofReal
                  (oneStepDirichletOverlapRemainderCoordinateSum
                    M n h p K j S omega hh ^ (4 : ℕ)))
            ∂M.P.toMeasure ≤ C := by
  obtain ⟨Cbig, hCbigTop, hbig⟩ :=
    exists_lintegral_oneStepDirichletOverlapLargeGradient_four_le d
  let c : ℝ≥0∞ := ENNReal.ofReal (8 * (d : ℝ) ^ (4 : ℕ))
  let U : ℝ≥0∞ := ENNReal.ofReal
    (oneStepSourceParentGradientConst ^ (4 : ℕ))
  let C : ℝ≥0∞ := c * (Cbig * U + U)
  have hcTop : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hUTop : U ≠ ∞ := ENNReal.ofReal_ne_top
  refine ⟨C, ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hcTop)
    (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top hCbigTop
      (lt_top_iff_ne_top.2 hUTop), lt_top_iff_ne_top.2 hUTop⟩), ?_⟩
  intro M n h p K j hh hp hblock
  let s := overlapCentersAtDepth (originCube d K) j
  let A : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ := fun omega ↦
    ((s.card : ℝ≥0∞)⁻¹) * ∑ S ∈ s,
      (oneStepDirichletOverlapLargeGradient M n h p K j S omega hh) ^ (4 : ℕ)
  let B : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ := fun omega ↦
    ((s.card : ℝ≥0∞)⁻¹) * ∑ S ∈ s,
      oneStepDirichletOverlapLocalGradientFourth M n h p K j S omega hh
  have hBmeas : Measurable B := by
    apply measurable_const.mul
    exact Finset.measurable_sum s fun S _hS ↦
      measurable_oneStepDirichletOverlapLocalGradientFourth M n h p K j S hh
  have hpoint : ∀ omega,
      ((s.card : ℝ≥0∞)⁻¹) * ∑ S ∈ s,
          ENNReal.ofReal
            (oneStepDirichletOverlapRemainderCoordinateSum
              M n h p K j S omega hh ^ (4 : ℕ)) ≤
        c * (A omega + B omega) := by
    intro omega
    calc
      _ ≤ ((s.card : ℝ≥0∞)⁻¹) * ∑ S ∈ s,
          c * ((oneStepDirichletOverlapLargeGradient
              M n h p K j S omega hh) ^ (4 : ℕ) +
            oneStepDirichletOverlapLocalGradientFourth
              M n h p K j S omega hh) := by
        gcongr with S hS
        simpa only [c] using!
          ofReal_oneStepDirichletOverlapRemainderCoordinateSum_pow_four_le
            M n h p K j S omega hh
      _ = c * (A omega + B omega) := by
        dsimp only [A, B]
        rw [← Finset.mul_sum]
        rw [Finset.sum_add_distrib]
        ring
  have hlarge : ∫⁻ omega, A omega ∂M.P.toMeasure ≤ Cbig * U := by
    have hr := oneStepRatioMinusOneEightBound_le_uniform M h hblock
    have hr0 := oneStepRatioMinusOneEightBound_nonneg M h
    have hratio :
        (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) ≤ U := by
      dsimp only [U]
      rw [show (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) =
          (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℕ) by
            exact ENNReal.rpow_natCast _ 4,
        ← ENNReal.ofReal_pow hr0]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hr0 hr 4)
    calc
      ∫⁻ omega, A omega ∂M.P.toMeasure ≤
          Cbig * (ENNReal.ofReal
            (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) := by
        dsimp only [A, s]
        convert hbig M n h p K j hh hp using 1
        apply lintegral_congr
        intro omega
        congr 1
        apply Finset.sum_congr rfl
        intro S hS
        exact (ENNReal.rpow_natCast _ 4).symm
      _ ≤ Cbig * U := by gcongr
  have hlocal : ∫⁻ omega, B omega ∂M.P.toMeasure ≤ U := by
    simpa only [B, s, U] using!
      lintegral_average_oneStepDirichletOverlapLocalGradientFourth_le_uniform
        M n h p K j hh hp hblock
  calc
    (∫⁻ omega, ((s.card : ℝ≥0∞)⁻¹) *
        (∑ S ∈ s, ENNReal.ofReal
          (oneStepDirichletOverlapRemainderCoordinateSum
            M n h p K j S omega hh ^ (4 : ℕ))) ∂M.P.toMeasure) ≤
      ∫⁻ omega, c * (A omega + B omega) ∂M.P.toMeasure :=
        lintegral_mono hpoint
    _ = c * ((∫⁻ omega, A omega ∂M.P.toMeasure) +
        ∫⁻ omega, B omega ∂M.P.toMeasure) := by
      rw [lintegral_const_mul' _ _ hcTop, lintegral_add_right A hBmeas]
    _ ≤ c * (Cbig * U + U) := by gcongr
    _ = C := rfl

/-- Neumann counterpart of the integrated nested-remainder sweep. -/
theorem exists_lintegral_oneStepNeumannOverlapRemainderCoordinateSum_four_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (K : ℤ) (j : ℕ) (hh : 0 < h)
        (_hp : vecNormSq p = 1) (_hblock : (h : ℝ) ≤ M.delta⁻¹),
        ∫⁻ omega,
            (((overlapCentersAtDepth (originCube d K) j).card : ℝ≥0∞)⁻¹) *
              (∑ S ∈ overlapCentersAtDepth (originCube d K) j,
                ENNReal.ofReal
                  (oneStepNeumannOverlapRemainderCoordinateSum
                    M n h p K j S omega hh ^ (4 : ℕ)))
            ∂M.P.toMeasure ≤ C := by
  obtain ⟨Cbig, hCbigTop, hbig⟩ :=
    exists_lintegral_oneStepNeumannOverlapLargeGradient_four_le d
  let c : ℝ≥0∞ := ENNReal.ofReal (8 * (d : ℝ) ^ (4 : ℕ))
  let U : ℝ≥0∞ := ENNReal.ofReal
    (oneStepSourceParentGradientConst ^ (4 : ℕ))
  let C : ℝ≥0∞ := c * (Cbig * U + U)
  have hcTop : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hUTop : U ≠ ∞ := ENNReal.ofReal_ne_top
  refine ⟨C, ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hcTop)
    (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top hCbigTop
      (lt_top_iff_ne_top.2 hUTop), lt_top_iff_ne_top.2 hUTop⟩), ?_⟩
  intro M n h p K j hh hp hblock
  let s := overlapCentersAtDepth (originCube d K) j
  let A : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ := fun omega ↦
    ((s.card : ℝ≥0∞)⁻¹) * ∑ S ∈ s,
      (oneStepNeumannOverlapLargeGradient M n h p K j S omega hh) ^ (4 : ℕ)
  let B : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ := fun omega ↦
    ((s.card : ℝ≥0∞)⁻¹) * ∑ S ∈ s,
      oneStepNeumannOverlapLocalGradientFourth M n h p K j S omega hh
  have hBmeas : Measurable B := by
    apply measurable_const.mul
    exact Finset.measurable_sum s fun S _hS ↦
      measurable_oneStepNeumannOverlapLocalGradientFourth M n h p K j S hh
  have hpoint : ∀ omega,
      ((s.card : ℝ≥0∞)⁻¹) * ∑ S ∈ s,
          ENNReal.ofReal
            (oneStepNeumannOverlapRemainderCoordinateSum
              M n h p K j S omega hh ^ (4 : ℕ)) ≤
        c * (A omega + B omega) := by
    intro omega
    calc
      _ ≤ ((s.card : ℝ≥0∞)⁻¹) * ∑ S ∈ s,
          c * ((oneStepNeumannOverlapLargeGradient
              M n h p K j S omega hh) ^ (4 : ℕ) +
            oneStepNeumannOverlapLocalGradientFourth
              M n h p K j S omega hh) := by
        gcongr with S hS
        simpa only [c] using!
          ofReal_oneStepNeumannOverlapRemainderCoordinateSum_pow_four_le
            M n h p K j S omega hh
      _ = c * (A omega + B omega) := by
        dsimp only [A, B]
        rw [← Finset.mul_sum]
        rw [Finset.sum_add_distrib]
        ring
  have hlarge : ∫⁻ omega, A omega ∂M.P.toMeasure ≤ Cbig * U := by
    have hr := oneStepRatioMinusOneEightBound_le_uniform M h hblock
    have hr0 := oneStepRatioMinusOneEightBound_nonneg M h
    have hratio :
        (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) ≤ U := by
      dsimp only [U]
      rw [show (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) =
          (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℕ) by
            exact ENNReal.rpow_natCast _ 4,
        ← ENNReal.ofReal_pow hr0]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hr0 hr 4)
    calc
      ∫⁻ omega, A omega ∂M.P.toMeasure ≤
          Cbig * (ENNReal.ofReal
            (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) := by
        dsimp only [A, s]
        convert hbig M n h p K j hh hp using 1
        apply lintegral_congr
        intro omega
        congr 1
        apply Finset.sum_congr rfl
        intro S hS
        exact (ENNReal.rpow_natCast _ 4).symm
      _ ≤ Cbig * U := by gcongr
  have hlocal : ∫⁻ omega, B omega ∂M.P.toMeasure ≤ U := by
    simpa only [B, s, U] using!
      lintegral_average_oneStepNeumannOverlapLocalGradientFourth_le_uniform
        M n h p K j hh hp hblock
  calc
    (∫⁻ omega, ((s.card : ℝ≥0∞)⁻¹) *
        (∑ S ∈ s, ENNReal.ofReal
          (oneStepNeumannOverlapRemainderCoordinateSum
            M n h p K j S omega hh ^ (4 : ℕ))) ∂M.P.toMeasure) ≤
      ∫⁻ omega, c * (A omega + B omega) ∂M.P.toMeasure :=
        lintegral_mono hpoint
    _ = c * ((∫⁻ omega, A omega ∂M.P.toMeasure) +
        ∫⁻ omega, B omega ∂M.P.toMeasure) := by
      rw [lintegral_const_mul' _ _ hcTop, lintegral_add_right A hBmeas]
    _ ≤ c * (Cbig * U + U) := by gcongr
    _ = C := rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
