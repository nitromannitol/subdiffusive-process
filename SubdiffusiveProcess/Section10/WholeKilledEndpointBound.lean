import SubdiffusiveProcess.Section10.KilledKernelSmoothing

/-! The actual whole-space endpoint expectation is controlled by strict
survival plus the bounded early-exit remainder, including exact-time ties.
The bound preserves the original law and arbitrary signed observables. -/

noncomputable section
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Section10

/-- The whole endpoint expectation is at most the actual killed expectation
plus the global bound times the original inclusive early-exit probability. -/
theorem whole_integral_le_killed_add_early_exit {d : ℕ}
    (P : SubMarkovKernelSemigroup (Vec d)) (hP : P.IsConservative)
    (K : Kernel (Vec d) (ContinuousPath (Vec d))) [IsMarkovKernel K]
    (hfdd : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel P I x)
    (U : Set (Vec d)) (hU : IsOpen U) (t : NNReal)
    (g : Vec d → ℝ) (hg : Measurable g) (F : ℝ) (hF : 0 ≤ F)
    (hgb : ∀ y, |g y| ≤ F) (x : Vec d) :
    (∫ y, g y ∂P t x) ≤
      kernelIntegral (killedKernel (K.map LifetimePath.ofContinuousPath) U hU t) g x +
        F * (K x {w | ContinuousPath.exitTime U w ≤ (t : ENNReal)}).toReal := by
  have hfdd' : ∀ I : Finset NNReal,
      K.map (ContinuousPath.finsetEvaluation I) =
        SubMarkovKernelSemigroup.finiteSetKernel P I := by
    intro I
    ext y B hB
    exact congrArg (fun m : Measure (I → Vec d) => m B) (hfdd I y)
  have heval : Measurable (fun w : ContinuousPath (Vec d) => w t) :=
    ContinuousPath.measurable_coordinateProcess t
  have hpathint : Integrable (fun w : ContinuousPath (Vec d) => g (w t)) (K x) := by
    apply (integrable_const F).mono (hg.comp heval).aestronglyMeasurable
    filter_upwards [] with w
    simpa only [Real.norm_eq_abs, abs_of_nonneg hF] using hgb (w t)
  have hsurv := ContinuousPath.measurableSet_lt_exitTime U hU t
  have hwhole : (∫ y, g y ∂P t x) = ∫ w, g (w t) ∂K x := by
    rw [← realization_map_eval P hP K hfdd' t,
      Kernel.map_apply _ heval, integral_map heval.aemeasurable hg.aestronglyMeasurable]
  have hcompl : {w : ContinuousPath (Vec d) | (t : ENNReal) < ContinuousPath.exitTime U w}ᶜ =
      {w | ContinuousPath.exitTime U w ≤ (t : ENNReal)} := by
    ext w
    simp only [mem_compl_iff, mem_setOf_eq, not_lt]
  have hrest : (∫ w in {w : ContinuousPath (Vec d) |
        (t : ENNReal) < ContinuousPath.exitTime U w}ᶜ, g (w t) ∂K x) ≤
      F * (K x {w | ContinuousPath.exitTime U w ≤ (t : ENNReal)}).toReal := by
    calc
      _ ≤ ∫ _w in {w : ContinuousPath (Vec d) |
          (t : ENNReal) < ContinuousPath.exitTime U w}ᶜ, F ∂K x :=
        integral_mono_ae hpathint.integrableOn (integrable_const F)
          (Filter.Eventually.of_forall fun w => (le_abs_self (g (w t))).trans (hgb (w t)))
      _ = _ := by
        rw [hcompl, setIntegral_const]
        simp only [measureReal_def, smul_eq_mul, mul_comm]
  change (∫ y, g y ∂P t x) ≤
    (∫ y, g y ∂killedKernel (K.map LifetimePath.ofContinuousPath) U hU t x) + _
  rw [hwhole, killedKernel_integral_ofContinuousPath K U hU t hg x,
    ← integral_add_compl hsurv hpathint]
  exact add_le_add le_rfl hrest

end SubdiffusiveProcess.Section10
