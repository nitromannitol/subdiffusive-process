module

public import MarkovProcess.Main
public import MarkovProcess.Restart.RationalRestart

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservative
variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]

omit [CompleteSpace alpha] [SecondCountableTopology alpha] [StandardBorelSpace alpha] [Nonempty alpha] in
/-- The given finite-dimensional realization starts at the supplied point. -/
theorem realization_map_eval_zero
    {alpha : Type*} [_portSection1 : MetricSpace alpha] [_portSection2 : CompleteSpace alpha] [_portSection3 : MeasurableSpace alpha] [_portSection4 : BorelSpace alpha] [_portSection5 : SecondCountableTopology alpha] [_portSection6 : StandardBorelSpace alpha] [_portSection7 : Nonempty alpha]
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q]
    (hfdd : ∀ I : Finset NNReal,
      Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I) :
    Q.map (fun path ↦ path (0 : NNReal)) = Kernel.id := by
  classical
  let I : Finset NNReal := {0}
  let z : I := ⟨0, Finset.mem_singleton_self 0⟩
  let i : Fin I.card := (I.orderIsoOfFin rfl).symm z
  let e : Fin 1 ↪o Fin I.card := OrderEmbedding.ofStrictMono (fun _ ↦ i) (by
    intro a b hab
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    simp only [ha, hb, lt_self_iff_false] at hab)
  have hfun : (fun path : ContinuousPath alpha ↦ path (0 : NNReal)) =
      (fun path : I → alpha ↦ path z) ∘ ContinuousPath.finsetEvaluation I := rfl
  have hEval : Measurable (ContinuousPath.finsetEvaluation (alpha := alpha) I) :=
    measurable_pi_iff.mpr fun t ↦ ContinuousPath.measurable_coordinateProcess t
  rw [hfun, Kernel.map_comp_right Q hEval
    (measurable_pi_apply z), hfdd I, finiteSetKernel_eq_map,
    ← Kernel.map_comp_right _ (measurable_orderedPathToFiniteSet I)
      (measurable_pi_apply z)]
  change (finiteTimeKernel P (finiteSetTimes I)).map (fun path ↦ path i) = _
  have hfun' : (fun path : Fin I.card → alpha ↦ path i) =
      (fun path : Fin 1 → alpha ↦ path 0) ∘ FiniteOrderedTimes.restrictPath e := rfl
  rw [hfun', Kernel.map_comp_right _ (FiniteOrderedTimes.measurable_restrictPath e)
    (measurable_pi_apply 0), hP.finiteTimeKernel_map_restrictPath P,
    finiteTimeKernel_one_map_eval]
  have htime : ((finiteSetTimes I).restrict e) 0 = 0 := by
    change ((I.orderIsoOfFin rfl ((I.orderIsoOfFin rfl).symm z) : I) : NNReal) = 0
    rw [OrderIso.apply_symm_apply]
  rw [htime, P.zero]

omit [CompleteSpace alpha] [SecondCountableTopology alpha] [StandardBorelSpace alpha] [Nonempty alpha] in
/-- Rational mixed coordinates inherit the finite-dimensional semigroup laws. -/
theorem realization_map_mixedPastShiftedCoordinates_restrict
    {alpha : Type*} [_portSection1 : MetricSpace alpha] [_portSection2 : CompleteSpace alpha] [_portSection3 : MeasurableSpace alpha] [_portSection4 : BorelSpace alpha] [_portSection5 : SecondCountableTopology alpha] [_portSection6 : StandardBorelSpace alpha] [_portSection7 : Nonempty alpha]
    (P : SubMarkovKernelSemigroup alpha) (_hP : P.IsConservative)
    (_default : ContinuousPath alpha)
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q]
    (hfdd : ∀ I : Finset NNReal,
      Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I)
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    Q.map (I.restrict ∘ ContinuousPath.mixedPastShiftedCoordinates S) =
      (finiteSetKernel P (MixedPastFuture.absolutePhysicalFinset S I)).map
        (MixedPastFuture.pullbackAbsolutePhysical S I) := by
  let evaluateAbsolute : ContinuousPath alpha →
      MixedPastFuture.absolutePhysicalFinset S I → alpha := fun path t ↦ path t
  have hEvaluateAbsolute : Measurable evaluateAbsolute := by
    rw [measurable_pi_iff]
    intro t
    exact ContinuousPath.measurable_coordinateProcess (alpha := alpha) t
  have hcoordinates : I.restrict ∘ ContinuousPath.mixedPastShiftedCoordinates S =
      MixedPastFuture.pullbackAbsolutePhysical S I ∘ evaluateAbsolute := by
    funext omega
    exact ContinuousPath.restrict_mixedPastShiftedCoordinates S I omega
  rw [hcoordinates, Kernel.map_comp_right]
  · change (Q.map (ContinuousPath.finsetEvaluation
      (MixedPastFuture.absolutePhysicalFinset S I))).map
      (MixedPastFuture.pullbackAbsolutePhysical S I) = _
    rw [hfdd]
  · exact hEvaluateAbsolute
  · exact MixedPastFuture.measurable_pullbackAbsolutePhysical S I
end MarkovProcess.SubMarkovKernelSemigroup.IsConservative
