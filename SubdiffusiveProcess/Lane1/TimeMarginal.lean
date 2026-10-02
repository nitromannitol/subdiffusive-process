import SubdiffusiveProcess.Main.DiffusionPath
import MarkovProcess.FiniteTime.ProjectiveFamily
import SubdiffusiveProcess.Inputs.MarkovProcesses
import MarkovProcess.Path.ExitTime

/-!
# The one-time marginal of a path law

The attachment predicate identifies the finite-dimensional distributions of
the path kernel with those of the semigroup.  At a singleton set of times that
identification is the statement that the law of the path at time `h` is the
transition kernel at time `h`, which is the form the moment bound consumes.
-/

open MeasureTheory MarkovProcess ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess

variable {alpha : Type*} [MeasurableSpace alpha]

/-- The unique coordinate of the singleton finite-set kernel is the transition
kernel at that time. -/
theorem finiteSetKernel_singleton_map_eval
    (P : SubMarkovKernelSemigroup alpha) (h : ℝ≥0) :
    (SubMarkovKernelSemigroup.finiteSetKernel P {h}).map
        (fun y : (({h} : Finset ℝ≥0)) → alpha =>
          y ⟨h, Finset.mem_singleton_self h⟩)
      = P.kernel h := by
  classical
  have hcard : ({h} : Finset ℝ≥0).card = 1 := rfl
  have hmev : Measurable (fun y : (({h} : Finset ℝ≥0)) → alpha =>
      y ⟨h, Finset.mem_singleton_self h⟩) := measurable_pi_apply _
  rw [SubMarkovKernelSemigroup.finiteSetKernel_eq_map, ← Kernel.map_comp_right _
    (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet _) hmev]
  have hfun : ((fun y : (({h} : Finset ℝ≥0)) → alpha =>
        y ⟨h, Finset.mem_singleton_self h⟩) ∘
      SubMarkovKernelSemigroup.orderedPathToFiniteSet ({h} : Finset ℝ≥0))
      = fun path : Fin 1 → alpha => path 0 := by
    funext path
    simp only [Function.comp_apply,
      SubMarkovKernelSemigroup.orderedPathToFiniteSet]
    congr 1
    exact Subsingleton.elim (α := Fin 1) _ _
  rw [hfun]
  have hone := SubMarkovKernelSemigroup.finiteTimeKernel_one_map_eval
      (α := alpha) P (SubMarkovKernelSemigroup.finiteSetTimes ({h} : Finset ℝ≥0))
  rw [hone]
  congr 1
  exact Finset.mem_singleton.mp (Finset.orderEmbOfFin_mem _ rfl _)

/-- From the singleton finite-dimensional identification to the law of the
path at a single time. -/
theorem map_eval_eq_of_finsetEvaluation {d : ℕ}
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (nu : Measure (DiffusionPath d)) (y : SpatialCoordinates d) (h : ℝ≥0)
    (hfdd : nu.map (ContinuousPath.finsetEvaluation ({h} : Finset ℝ≥0))
      = SubMarkovKernelSemigroup.finiteSetKernel P ({h} : Finset ℝ≥0) y) :
    nu.map (fun path : DiffusionPath d => path h) = P.kernel h y := by
  classical
  have hev : Measurable
      (ContinuousPath.finsetEvaluation (alpha := SpatialCoordinates d)
        ({h} : Finset ℝ≥0)) :=
    measurable_pi_lambda _ fun t =>
      (continuous_eval_const ((t : ℝ≥0))).measurable
  have hmev : Measurable (fun w : (({h} : Finset ℝ≥0)) → SpatialCoordinates d =>
      w ⟨h, Finset.mem_singleton_self h⟩) := measurable_pi_apply _
  have hcomp : (fun w : (({h} : Finset ℝ≥0)) → SpatialCoordinates d =>
        w ⟨h, Finset.mem_singleton_self h⟩) ∘
      ContinuousPath.finsetEvaluation (alpha := SpatialCoordinates d)
        ({h} : Finset ℝ≥0)
      = fun path : DiffusionPath d => path h := rfl
  calc nu.map (fun path : DiffusionPath d => path h)
      = nu.map ((fun w : (({h} : Finset ℝ≥0)) → SpatialCoordinates d =>
          w ⟨h, Finset.mem_singleton_self h⟩) ∘
          ContinuousPath.finsetEvaluation ({h} : Finset ℝ≥0)) := by rw [hcomp]
    _ = (nu.map (ContinuousPath.finsetEvaluation ({h} : Finset ℝ≥0))).map
          (fun w => w ⟨h, Finset.mem_singleton_self h⟩) :=
        (Measure.map_map hmev hev).symm
    _ = (SubMarkovKernelSemigroup.finiteSetKernel P ({h} : Finset ℝ≥0) y).map
          (fun w => w ⟨h, Finset.mem_singleton_self h⟩) := by rw [hfdd]
    _ = P.kernel h y := by
        rw [← Kernel.map_apply _ hmev, finiteSetKernel_singleton_map_eval]

end SubdiffusiveProcess
