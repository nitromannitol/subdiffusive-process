module

public import SubdiffusiveProcess.Model.PotentialField
public import Homogenization.Ambient.ScalarMatrix
public import Homogenization.Probability.RegCoeffField.Sigma
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Scalar potential field API

Topological, differential, and scalar-coefficient support for the potential
carrier used in paper label `a.g2`.
-/



namespace SubdiffusiveProcess.Model

open Homogenization MeasureTheory Topology

noncomputable section

noncomputable instance potentialFieldTopologicalSpace (d : ℕ) :
    TopologicalSpace (PotentialField d) :=
  TopologicalSpace.induced Subtype.val inferInstance

noncomputable instance potentialFieldMeasurableSpace (d : ℕ) :
    MeasurableSpace (PotentialField d) :=
  borel (PotentialField d)

instance potentialFieldBorelSpace (d : ℕ) : BorelSpace (PotentialField d) :=
  ⟨rfl⟩

namespace PotentialField

variable {d : ℕ}

instance : CoeFun (PotentialField d) (fun _ ↦ Vec d → ℝ) :=
  ⟨fun g ↦ g.1.1⟩

/-- The continuous first derivative stored in a potential field. -/
def deriv (g : PotentialField d) : C(Vec d, Vec d →L[ℝ] ℝ) :=
  g.1.2

theorem hasFDerivAt (g : PotentialField d) (x : Vec d) :
    HasFDerivAt g (deriv g x) x :=
  g.2.1 x

/-- The stored compact-set certificate implies the usual local Lipschitz
condition on the derivative. -/
theorem deriv_locallyLipschitz (g : PotentialField d) :
    LocallyLipschitz (deriv g) := by
  intro x
  obtain ⟨C, hC⟩ := g.2.2 (Metric.closedBall x 1) (isCompact_closedBall x 1)
  exact ⟨C, Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one,
    hC.mono Metric.ball_subset_closedBall⟩

/-- Every potential in the carrier is continuously differentiable. -/
theorem contDiff_one (g : PotentialField d) : ContDiff ℝ 1 g :=
  contDiff_one_iff_hasFDerivAt.mpr
    ⟨deriv g, g.deriv_locallyLipschitz.continuous, g.hasFDerivAt⟩

/-- Potential values determine their stored derivative and certificates. -/
@[ext]
theorem ext {g h : PotentialField d} (heq : ∀ x, g x = h x) : g = h := by
  have hval : g.1.1 = h.1.1 := ContinuousMap.ext heq
  have hderiv : g.1.2 = h.1.2 := by
    apply ContinuousMap.ext
    intro x
    exact (g.hasFDerivAt x).unique (by simpa only [deriv, hval] using h.hasFDerivAt x)
  apply Subtype.ext
  exact Prod.ext hval hderiv

theorem continuous_eval (x : Vec d) :
    Continuous (fun g : PotentialField d ↦ g x) :=
  (continuous_eval_const x).comp continuous_subtype_val.fst

theorem measurable_eval (x : Vec d) :
    Measurable (fun g : PotentialField d ↦ g x) :=
  (continuous_eval x).measurable

theorem continuous_eval_deriv (x : Vec d) :
    Continuous (fun g : PotentialField d ↦ deriv g x) :=
  (continuous_eval_const x).comp continuous_subtype_val.snd

/-- Embed a scalar potential as the coefficient field `g(x) I`. -/
def forgetPotential (g : PotentialField d) : RegCoeffField d where
  toFun x := scalarMatrix (d := d) (g x)
  entry_measurable := fun i k ↦ by
    have hmat : Continuous (fun x : Vec d ↦ scalarMatrix (d := d) (g x)) :=
      g.1.1.continuous.smul continuous_const
    exact ((continuous_apply k).comp ((continuous_apply i).comp hmat)).measurable
  entry_locInt := fun i k ↦ by
    have hmat : Continuous (fun x : Vec d ↦ scalarMatrix (d := d) (g x)) :=
      g.1.1.continuous.smul continuous_const
    exact ((continuous_apply k).comp ((continuous_apply i).comp hmat)).locallyIntegrable

@[simp]
theorem forgetPotential_apply (g : PotentialField d) (x : Vec d) :
    forgetPotential g x = scalarMatrix (d := d) (g x) :=
  rfl

private theorem measurable_forgetPotential_entryTest (i k : Fin d)
    (phi : Vec d → ℝ) (hphi : IsProbeR phi) :
    Measurable (fun g : PotentialField d ↦ entryTestR i k phi (forgetPotential g)) := by
  let F : PotentialField d × Vec d → ℝ :=
    fun q ↦ scalarMatrix (d := d) (q.1 q.2) i k * phi q.2
  have hval : Continuous (fun q : PotentialField d × Vec d ↦ q.1 q.2) :=
    ContinuousEval.continuous_eval.comp
      (((continuous_subtype_val.comp continuous_fst).fst).prodMk continuous_snd)
  have hmat : Continuous
      (fun q : PotentialField d × Vec d ↦ scalarMatrix (d := d) (q.1 q.2)) :=
    hval.smul continuous_const
  have hFmeas : Measurable F :=
    (((continuous_apply k).comp ((continuous_apply i).comp hmat)).measurable).mul
      (hphi.measurable.comp measurable_snd)
  have hInt : StronglyMeasurable
      (fun g : PotentialField d ↦ ∫ x, F (g, x) ∂volume) :=
    hFmeas.stronglyMeasurable.integral_prod_right'
  have hEq : (fun g : PotentialField d ↦ ∫ x, F (g, x) ∂volume) =
      fun g ↦ entryTestR i k phi (forgetPotential g) := by
    funext g
    rfl
  rw [← hEq]
  exact hInt.measurable

theorem measurable_forgetPotential :
    Measurable (forgetPotential (d := d)) := by
  refine measurable_into_regCoeffField' ?_ ?_
  · intro x i k
    have hmat : Continuous
        (fun g : PotentialField d ↦ scalarMatrix (d := d) (g x)) :=
      (continuous_eval x).smul continuous_const
    exact ((continuous_apply k).comp ((continuous_apply i).comp hmat)).measurable
  · intro i k phi hphi
    exact measurable_forgetPotential_entryTest i k phi hphi

end PotentialField

end

end SubdiffusiveProcess.Model
