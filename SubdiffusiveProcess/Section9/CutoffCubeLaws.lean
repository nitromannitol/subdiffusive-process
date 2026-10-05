
module

public import Mathlib.Probability.IdentDistrib

public import SubdiffusiveProcess.Section9.CutoffOneCubeTail
public import SubdiffusiveProcess.Section9.CutoffCubeLocalMeasurability
public import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffRange
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.CubeTranslationTransport

@[expose] public section

/-! # Translation laws and finite-range independence for cutoff cube averages -/

namespace SubdiffusiveProcess.Section9

open Homogenization MeasureTheory ProbabilityTheory
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- The normalized finite-cutoff average on an arbitrary triadic cube. -/
noncomputable def cutoffCubeAverage (M : GMCModel d) (L : ℕ)
    (Q : Homogenization.TriadicCube d) (omega : PotentialSample d) : ℝ :=
  cubeAverage Q (aCutoff M L omega)

theorem measurable_cutoffCubeAverage (M : GMCModel d) (L : ℕ)
    (Q : Homogenization.TriadicCube d) : Measurable (cutoffCubeAverage M L Q) := by
  unfold cutoffCubeAverage
  simp_rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  exact (measurable_cutoff_uncurry M L).stronglyMeasurable.integral_prod_right'.measurable

theorem cutoffCubeAverage_eq_origin_translate (M : GMCModel d) (L : ℕ)
    (Q : Homogenization.TriadicCube d) (omega : PotentialSample d) :
    cutoffCubeAverage M L Q omega =
      cutoffCubeAverage M L (originCube d Q.scale)
        (translatePotentialSequence (triadicCubeShift Q) omega) := by
  unfold cutoffCubeAverage
  rw [← cubeAverage_originCube_comp_addRight_eq Q]
  apply congrArg (cubeAverage (originCube d Q.scale))
  funext x
  exact (aCutoff_translatePotentialSequence M L (triadicCubeShift Q) omega x).symm

/-- Cube averages at the same scale have the exact stationary law. -/
theorem cutoffCubeAverage_identDistrib_origin (M : GMCModel d) (L : ℕ)
    (Q : Homogenization.TriadicCube d) :
    IdentDistrib (cutoffCubeAverage M L Q)
      (cutoffCubeAverage M L (originCube d Q.scale)) M.P.toMeasure M.P.toMeasure := by
  let T := translatePotentialSequence (d := d) (triadicCubeShift Q)
  let F := cutoffCubeAverage M L (originCube d Q.scale)
  have hpoint : cutoffCubeAverage M L Q = F ∘ T := by
    funext omega
    exact cutoffCubeAverage_eq_origin_translate M L Q omega
  refine ⟨(measurable_cutoffCubeAverage M L Q).aemeasurable,
    (measurable_cutoffCubeAverage M L (originCube d Q.scale)).aemeasurable, ?_⟩
  rw [hpoint]
  calc
    Measure.map (F ∘ T) M.P.toMeasure =
        Measure.map F (Measure.map T M.P.toMeasure) := by
      exact (Measure.map_map
        (measurable_cutoffCubeAverage M L (originCube d Q.scale))
        (measurable_translatePotentialSequence (triadicCubeShift Q))).symm
    _ = Measure.map F M.P.toMeasure := by
      rw [show Measure.map T M.P.toMeasure = M.P.toMeasure by
        exact potentialSequenceLaw_stationary M (triadicCubeShift Q)]
    _ = Measure.map (cutoffCubeAverage M L (originCube d Q.scale)) M.P.toMeasure := rfl

theorem cutoffCubeAverage_identDistrib_originCubeAverage (M : GMCModel d) (m : ℕ)
    (Q : Homogenization.TriadicCube d) (hQ : Q.scale = (m : ℤ)) :
    IdentDistrib (cutoffCubeAverage M m Q) (cutoffOriginCubeAverage M m)
      M.P.toMeasure M.P.toMeasure := by
  have heq : cutoffCubeAverage M m (originCube d Q.scale) =
      cutoffOriginCubeAverage M m := by
    funext omega
    unfold cutoffCubeAverage cutoffOriginCubeAverage
    rw [cubeAverage_eq_integral_normalizedCubeMeasure, hQ]
  rw [← heq]
  exact cutoffCubeAverage_identDistrib_origin M m Q

private theorem measurable_aCutoff_eval_from_cubeLocalSigma (M : GMCModel d) (L : ℕ)
    (Q : Homogenization.TriadicCube d) {x : Homogenization.Vec d}
    (hx : x ∈ openCubeSet Q) :
    @Measurable (PotentialSample d) ℝ
      (aCutoffPotentialLocalSigma L (openCubeSet Q)) _
      (fun omega ↦ aCutoff M L omega x) := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)⟩
  have hcoord (k : Fin (L + 1)) :
      @Measurable (PotentialSample d) (PotentialField d)
        (aCutoffPotentialLocalSigma L (openCubeSet Q))
        (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma (openCubeSet Q)) (fun omega ↦ omega k) :=
    Measurable.of_comap_le (le_iSup (fun q : Fin (L + 1) ↦
      (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma (openCubeSet Q)).comap
        (fun omega : PotentialSample d ↦ omega q)) k)
  have heval (k : Fin (L + 1)) :
      @Measurable (PotentialSample d) ℝ
        (aCutoffPotentialLocalSigma L (openCubeSet Q)) _
        (fun omega ↦ omega k x) :=
    (measurable_eval_potentialFieldLocalSigma_of_mem_isOpen
      (isOpen_openCubeSet Q) hx).comp (hcoord k)
  unfold aCutoff
  apply Measurable.exp
  refine Finset.measurable_sum (Finset.range (L + 1)) fun k hk ↦ ?_
  exact (heval ⟨k, Finset.mem_range.mp hk⟩).sub_const _

private theorem measurable_cutoff_setIntegral_cubeLocalSigma
    (M : GMCModel d) (L : ℕ) (Q : Homogenization.TriadicCube d) :
    @Measurable (PotentialSample d) ℝ
      (aCutoffPotentialLocalSigma L (openCubeSet Q)) _
      (fun omega ↦ ∫ x in openCubeSet Q, aCutoff M L omega x ∂volume) := by
  let : MeasurableSpace (PotentialSample d) :=
    aCutoffPotentialLocalSigma L (openCubeSet Q)
  let muU : Measure (Homogenization.Vec d) :=
    volume.restrict (openCubeSet Q)
  let : IsFiniteMeasure muU := ⟨by
    dsimp only [muU]
    rw [Measure.restrict_apply_univ]
    exact volume_openCubeSet_lt_top Q⟩
  have hInt := measurable_integral_of_continuous_of_measurable
    (Measure.comap Subtype.val muU)
    (fun omega (x : openCubeSet Q) ↦ aCutoff M L omega x)
    (fun omega ↦ (continuous_aCutoff M L omega).comp continuous_subtype_val)
    (fun x ↦ measurable_aCutoff_eval_from_cubeLocalSigma M L Q x.property)
  have heq : (fun omega : PotentialSample d ↦
      ∫ x : openCubeSet Q, aCutoff M L omega x ∂(Measure.comap Subtype.val muU)) =
      fun omega ↦ ∫ x in openCubeSet Q, aCutoff M L omega x ∂volume := by
    funext omega
    rw [integral_subtype_comap (isOpen_openCubeSet Q).measurableSet]
    change ∫ x, aCutoff M L omega x
        ∂((volume.restrict (openCubeSet Q)).restrict (openCubeSet Q)) =
      ∫ x, aCutoff M L omega x ∂(volume.restrict (openCubeSet Q))
    rw [Measure.restrict_restrict_of_subset Set.Subset.rfl]
  rw [heq] at hInt
  exact hInt

/-- A cutoff cube average is measurable from precisely the cutoff information
on the cube interior. Boundary values do not enter the Lebesgue integral. -/
theorem measurable_cutoffCubeAverage_cubeLocalSigma (M : GMCModel d) (L : ℕ)
    (Q : Homogenization.TriadicCube d) :
    @Measurable (PotentialSample d) ℝ
      (aCutoffPotentialLocalSigma L (openCubeSet Q)) _
      (cutoffCubeAverage M L Q) := by
  have hset := measurable_cutoff_setIntegral_cubeLocalSigma M L Q
  rw [show cutoffCubeAverage M L Q = fun omega ↦
      (cubeVolume Q)⁻¹ * ∫ x in openCubeSet Q, aCutoff M L omega x ∂volume by
    funext omega
    unfold cutoffCubeAverage cubeAverage
    rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet]]
  exact hset.const_mul _

/-- Finite-range independence of the two actual normalized cutoff averages. -/
theorem indepFun_cutoffCubeAverage_of_separation (M : GMCModel d) (L : ℕ)
    (Q R : Homogenization.TriadicCube d)
    (hsep : ∀ ⦃x y : Homogenization.Vec d⦄,
      x ∈ openCubeSet Q → y ∈ openCubeSet R →
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ L ≤
        Homogenization.Book.Ch02.vecNorm (x - y)) :
    IndepFun (cutoffCubeAverage M L Q) (cutoffCubeAverage M L R) M.P.toMeasure := by
  have hindep := indep_aCutoffPotentialLocalSigma_of_separation M L
    (openCubeSet Q) (openCubeSet R) (isOpen_openCubeSet Q).measurableSet
      (isOpen_openCubeSet R).measurableSet hsep
  exact indep_of_indep_of_le_right
    (indep_of_indep_of_le_left hindep
      (measurable_cutoffCubeAverage_cubeLocalSigma M L Q).comap_le)
    (measurable_cutoffCubeAverage_cubeLocalSigma M L R).comap_le

end

end SubdiffusiveProcess.Section9
