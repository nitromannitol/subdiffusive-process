module

public import SubdiffusiveProcess.PartProcess.Exhaustion

@[expose] public section

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.PartProcess
open SubdiffusiveProcess.E7
variable {d : ℕ} {m : Measure (Fin d → ℝ)}

theorem killedOcc_indicator
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ))) (hK : IsMarkovKernel K)
    (U : Set (Fin d → ℝ)) (hU : IsOpen U) (α : ℝ)
    (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) (x : Fin d → ℝ) :
    killedOcc K U α (U.indicator f) x = killedOcc K U α f x := by
  rw [killedOcc_continuousPath, killedOcc_continuousPath]
  apply lintegral_congr
  intro t
  congr 1
  apply setLIntegral_congr_fun
    (measurableSet_lt measurable_const (ContinuousPath.measurable_exitTime U hU))
  intro w hw
  dsimp only
  rw [Set.indicator_of_mem (ContinuousPath.mem_of_lt_exitTime U w (Real.toNNReal t) hw)]

/-- Identification on the restricted measure for every part-form resolvent. -/
theorem part_association (hm : IsLocallyFiniteMeasure m) (hpos : m.IsOpenPosMeasure)
    (D : Data d m) (U : Set (Fin d → ℝ)) (hU : IsOpen U)
    (F : DirichletForm.ClosedForm (m.restrict U))
    (hF : IsPartFormOn D.form.toClosedForm U F)
    (α : ℝ) (hα : 0 < α)
    (G : Lp ℝ 2 (m.restrict U) →L[ℝ] Lp ℝ 2 (m.restrict U))
    (hG : DirichletForm.IsResolvent F α G)
    (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfL : MemLp f 2 (m.restrict U)) :
    (∀ᵐ x ∂(m.restrict U), killedOcc D.law U α f x < ⊤) ∧
    (fun x => (killedOcc D.law U α f x).toReal) =ᵐ[m.restrict U] ⇑(G (hfL.toLp f)) := by
  let f₀ : (Fin d → ℝ) → ℝ := U.indicator f
  have hf₀ : Measurable f₀ := hf.indicator hU.measurableSet
  have hf₀L : MemLp f₀ 2 m := (memLp_indicator_iff_restrict hU.measurableSet).2 hfL
  have hf₀0 : ∀ x, 0 ≤ f₀ x := fun x => indicator_nonneg (fun x _ => hf0 x) x
  let H := (extension U hU.measurableSet).comp (G.comp (restriction U))
  have hH : IsDomainResolvent D.form.toClosedForm
      (D.form.toClosedForm.killedCoreClosure U) α H :=
    part_resolvent_extension D.form.toClosedForm U hU F hF α G hG
  obtain ⟨hfinite, heq⟩ := open_association hm hpos D U hU α hα H hH
    f₀ hf₀ hf₀0 hf₀L
  have hrestrict : restrictLp U (hf₀L.toLp f₀) = hfL.toLp f := by
    apply Lp.ext
    filter_upwards [restrictLp_coe U (hf₀L.toLp f₀), hf₀L.coeFn_toLp.restrict,
      hfL.coeFn_toLp, ae_restrict_mem hU.measurableSet] with x hr he hf hx
    rw [hr, he, hf]
    exact indicator_of_mem hx f
  have hvalue : H (hf₀L.toLp f₀) = extendLp U hU.measurableSet (G (hfL.toLp f)) := by
    change extendLp U hU.measurableSet (G (restrictLp U (hf₀L.toLp f₀))) = _
    rw [hrestrict]
  constructor
  · filter_upwards [ae_restrict_of_ae hfinite] with x hx
    simpa only [f₀, killedOcc_indicator D.law D.markov U hU α f hf] using hx
  · filter_upwards [heq.restrict,
      (extendLp_coe U hU.measurableSet (G (hfL.toLp f))).restrict,
      ae_restrict_mem hU.measurableSet] with x hx he hxU
    rw [hvalue] at hx
    have hkill : killedOcc D.law U α f₀ x = killedOcc D.law U α f x :=
      killedOcc_indicator D.law D.markov U hU α f hf x
    rw [hkill] at hx
    exact hx.trans (he.trans (Set.indicator_of_mem hxU _))

theorem exists_part_with_association (hm : IsLocallyFiniteMeasure m)
    (hpos : m.IsOpenPosMeasure) (D : Data d m)
    (U : Set (Fin d → ℝ)) (hU : IsOpen U) :
    ∃ F : DirichletForm.ClosedForm (m.restrict U),
      IsPartFormOn D.form.toClosedForm U F ∧
      ∀ (α : ℝ), 0 < α →
        ∀ G : Lp ℝ 2 (m.restrict U) →L[ℝ] Lp ℝ 2 (m.restrict U),
          DirichletForm.IsResolvent F α G →
          ∀ (f : (Fin d → ℝ) → ℝ), Measurable f → (∀ x, 0 ≤ f x) →
            ∀ hf : MemLp f 2 (m.restrict U),
              (∀ᵐ x ∂(m.restrict U), killedOcc D.law U α f x < ⊤) ∧
              (fun x => (killedOcc D.law U α f x).toReal) =ᵐ[m.restrict U]
                ⇑(G (hf.toLp f)) := by
  obtain ⟨F, hF⟩ := exists_partForm d m hm hpos D.form D.regular U hU
  exact ⟨F, hF, fun α hα G hG f hf hf0 hfL =>
    part_association hm hpos D U hU F hF α hα G hG f hf hf0 hfL⟩

end SubdiffusiveProcess.PartProcess
