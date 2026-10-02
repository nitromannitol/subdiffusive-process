import SubdiffusiveProcess.Main.DiffusionPath
import MarkovProcess.FiniteTime.ProjectiveFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace Paper



theorem determining_functional_identity_finite_set_product_integral
    {d : Nat}
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hP : P.IsConservative)
    (I : Finset NNReal)
    (g : I → BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (x : SpatialCoordinates d) :
    (∫ y, ∏ t : I, g t (y t) ∂
      SubMarkovKernelSemigroup.finiteSetKernel P I x) =
      ∫ path, ∏ i : Fin I.card,
        g ⟨SubMarkovKernelSemigroup.finiteSetTimes I i,
          Finset.orderEmbOfFin_mem I rfl i⟩ (path i) ∂
        SubMarkovKernelSemigroup.finiteTimeKernel P
          (SubMarkovKernelSemigroup.finiteSetTimes I) x := by
  classical
  let F : (I → SpatialCoordinates d) → ℝ := fun y => ∏ t : I, g t (y t)
  have hF : Measurable F := by
    exact Finset.univ.measurable_fun_prod fun t _ =>
      (g t).measurable.comp (measurable_pi_apply t)
  have hF_ae : AEStronglyMeasurable F
      (Measure.map (SubMarkovKernelSemigroup.orderedPathToFiniteSet I)
        (SubMarkovKernelSemigroup.finiteTimeKernel P
          (SubMarkovKernelSemigroup.finiteSetTimes I) x)) :=
    hF.aestronglyMeasurable
  rw [SubMarkovKernelSemigroup.finiteSetKernel_eq_map]
  rw [Kernel.map_apply _
    (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet
      (α := SpatialCoordinates d) I)]
  rw [MeasureTheory.integral_map
    (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet
      (α := SpatialCoordinates d) I).aemeasurable hF_ae]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with path
  dsimp [F, SubMarkovKernelSemigroup.orderedPathToFiniteSet]
  apply Fintype.prod_equiv (I.orderIsoOfFin rfl).symm
  intro t
  congr 2
  apply Subtype.ext
  change (t : NNReal) =
    (I.orderEmbOfFin rfl) ((I.orderIsoOfFin rfl).symm t)
  rw [← Finset.coe_orderIsoOfFin_apply]
  exact congrArg (fun u : I => (u : NNReal))
    (OrderIso.apply_symm_apply (I.orderIsoOfFin rfl) t).symm

end Paper
end

