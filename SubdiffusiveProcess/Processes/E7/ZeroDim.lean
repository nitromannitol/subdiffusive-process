module

public import SubdiffusiveProcess.Probability.Diffusion.AnalyticInput
public import MarkovProcess.Main
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

@[expose] public section



open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.E7
open SubdiffusiveProcess.Probability.Diffusion.Input

theorem aux_n8z_eq_zero (x : Fin 0 → ℝ) : x = 0 := Subsingleton.elim _ _

theorem aux_n8z_exitTime_univ (ω : ContinuousPath (Fin 0 → ℝ)) :
    ContinuousPath.exitTime (univ : Set (Fin 0 → ℝ)) ω = ⊤ := by
  rw [ContinuousPath.exitTime]
  convert sInf_empty (α := ℝ≥0∞) using 2
  ext s
  simp

theorem aux_n8z_occupation_univ (K : Kernel (Fin 0 → ℝ) (ContinuousPath (Fin 0 → ℝ)))
    [IsMarkovKernel K] (s : ℝ) (hs : 0 < s) (f : (Fin 0 → ℝ) → ℝ) (x : Fin 0 → ℝ) :
    occupationResolvent (K.map LifetimePath.ofContinuousPath) univ s f x = f 0 := by
  have hA : ∀ t : ℝ, MeasurableSet {w : LifetimePath (Fin 0 → ℝ) |
      ENNReal.ofReal t < LifetimePath.exitTime univ w} := fun t =>
    measurableSet_lt measurable_const
      (show Measurable (LifetimePath.exitTime (univ : Set (Fin 0 → ℝ))) from
        (LifetimePath.isStoppingTime_exitTime (univ : Set (Fin 0 → ℝ)) isOpen_univ).measurable')
  have hinner : ∀ t : ℝ, ∫ w in {w | ENNReal.ofReal t < LifetimePath.exitTime univ w},
      f (stateAt (Real.toNNReal t) w) ∂(K.map LifetimePath.ofContinuousPath x) = f 0 := by
    intro t
    have hconst : ∀ w : LifetimePath (Fin 0 → ℝ), f (stateAt (Real.toNNReal t) w) = f 0 :=
      fun w => by rw [aux_n8z_eq_zero (stateAt _ w)]
    simp_rw [hconst]
    rw [setIntegral_const, measureReal_def, Kernel.map_apply K LifetimePath.measurable_ofContinuousPath x,
      Measure.map_apply LifetimePath.measurable_ofContinuousPath (hA t)]
    have hpre : LifetimePath.ofContinuousPath ⁻¹'
        {w : LifetimePath (Fin 0 → ℝ) | ENNReal.ofReal t < LifetimePath.exitTime univ w} = univ := by
      ext ω
      simp [aux_n8z_exitTime_univ]
    rw [hpre, measure_univ]
    simp
  unfold occupationResolvent
  simp_rw [hinner]
  have hexp : ∫ t in Ioi (0 : ℝ), Real.exp (-t / s) * f 0 = s * f 0 := by
    rw [integral_mul_const]
    have h := integral_exp_mul_Ioi (a := -s⁻¹) (by simpa using hs) 0
    have heq : (fun t : ℝ => Real.exp (-t / s)) = fun t => Real.exp (-s⁻¹ * t) := by
      funext t; congr 1; field_simp
    rw [heq, h]
    field_simp
    simp
  rw [hexp]
  field_simp

theorem killedGenerator_zero_dim (c rho : (Fin 0 → ℝ) → ℝ)
    (K : Kernel (Fin 0 → ℝ) (ContinuousPath (Fin 0 → ℝ))) [IsMarkovKernel K] :
    KilledGenerator c rho (K.map LifetimePath.ofContinuousPath) := by
  intro U hU _hUb s hs f _hf
  rcases Set.eq_empty_or_nonempty U with hUe | ⟨z, hz⟩
  · -- `U = ∅`: everything is over the empty set
    subst hUe
    refine ⟨fun _ => 0, fun _ => 0, ⟨?_⟩, by simp [Filter.EventuallyEq], fun ψ _ _ _ => by simp⟩
    exact
      { memLp := by simp
        grad_memLp := fun i => by simp
        approx := fun _ _ => 0
        smooth := fun _ => contDiff_const
        compactSupport := fun _ => HasCompactSupport.zero
        support_subset := fun _ => by simp
        tendsto_fun := by simp
        tendsto_grad := fun i => by simp }
  · -- `U = univ`
    have hUu : U = univ := by
      ext y; simp only [mem_univ, iff_true]
      rwa [aux_n8z_eq_zero y, ← aux_n8z_eq_zero z]
    subst hUu
    have hcpt : ∀ g : (Fin 0 → ℝ) → ℝ, HasCompactSupport g := fun g =>
      isCompact_univ.of_isClosed_subset (isClosed_tsupport g) (subset_univ _)
    refine ⟨fun _ => f 0, fun _ => 0, ⟨?_⟩, ?_, fun ψ _ _ _ => ?_⟩
    · exact
        { memLp := (continuous_const.memLp_of_hasCompactSupport (hcpt _)).restrict _
          grad_memLp := fun i => by simp
          approx := fun _ _ => f 0
          smooth := fun _ => contDiff_const
          compactSupport := fun _ => hcpt _
          support_subset := fun _ => subset_univ _
          tendsto_fun := by simp
          tendsto_grad := fun i => by simp }
    · exact Eventually.of_forall fun x => (aux_n8z_occupation_univ K s hs f x).symm
    · simp

end SubdiffusiveProcess.E7
