
module

public import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.AnchoredClauses
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.GoodSetMeasurable
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellSummable
public import Mathlib.Probability.StrongLaw

@[expose] public section

/-! # Strong law for pointwise shell values -/

namespace SubdiffusiveProcess.Section9

open Filter Homogenization Homogenization.IndependentSums MeasureTheory ProbabilityTheory
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- The actual shell values at the origin obey the pointwise strong law. -/
theorem ae_tendsto_pointwiseShellAverage_zero (M : GMCModel d) :
    ∀ᵐ omega ∂M.P.toMeasure,
      Tendsto (fun m : ℕ ↦
        (∑ k ∈ Finset.range (m + 1), omega k 0) / ((m : ℝ) + 1))
        atTop (nhds 0) := by
  let X : ℕ → PotentialSample d → ℝ := fun k omega ↦ omega k 0
  have hmeas : ∀ k, Measurable (X k) := fun k ↦
    _root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval 0 |>.comp (measurable_potentialCoordinate k)
  have hindepAll : iIndepFun X M.P.toMeasure := by
    exact M.shellPrefix.independent.comp
      (fun _ g ↦ g 0) (fun _ ↦ _root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval 0)
  have hindep : Pairwise (Function.onFun (fun f g ↦ f ⟂ᵢ[M.P.toMeasure] g) X) := by
    intro i j hij
    exact hindepAll.indepFun hij
  have hident : ∀ k, IdentDistrib (X k) (X 0) M.P.toMeasure M.P.toMeasure := by
    intro k
    refine ⟨(hmeas k).aemeasurable, (hmeas 0).aemeasurable, ?_⟩
    rw [map_potentialCoordinate_apply_eq_zero M k 0,
      map_potentialCoordinate_apply_eq_zero M 0 0]
  have hint : Integrable (X 0) M.P.toMeasure := by
    simpa only [X] using M.G1.integrable 0
  have hslln := strong_law_ae_real X hint hindep hident
  have hmean : ∫ omega, X 0 omega ∂M.P.toMeasure = 0 := by
    simpa only [X] using M.G1.mean_zero 0
  filter_upwards [hslln] with omega homega
  rw [hmean] at homega
  convert homega.comp (tendsto_add_atTop_nat 1) using 1
  funext m
  simp only [X, Function.comp_apply, Nat.cast_add, Nat.cast_one]

/-- The same strong law on the canonical anchored carrier. -/
theorem ae_tendsto_pointwiseShellAverage_zero_anchored (M : GMCModel d) :
    ∀ᵐ omega ∂(anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
      (measure_anchoredC11GoodSet_eq_one M)).toMeasure,
      Tendsto (fun m : ℕ ↦
        (∑ k ∈ Finset.range (m + 1), omega.val k 0) / ((m : ℝ) + 1))
        atTop (nhds 0) := by
  exact ae_anchoredC11SampleLaw_of_ae M (measurableSet_anchoredC11GoodSet d)
    (measure_anchoredC11GoodSet_eq_one M) (ae_tendsto_pointwiseShellAverage_zero M)

end

end SubdiffusiveProcess.Section9
