import SubdiffusiveProcess.PartProcess.LpRestriction
import Mathlib.MeasureTheory.Function.ContinuousMapDense

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.PartProcess
open SubdiffusiveProcess.E7

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

omit [TopologicalSpace X] in
theorem tendsto_Lp_of_energy (E : DirichletForm.ClosedForm m)
    {u : ℕ → Lp ℝ 2 m} {v : Lp ℝ 2 m} (hu : ∀ n, u n ∈ E.domain)
    (hv : v ∈ E.domain)
    (h : Tendsto (fun n => E.energyNormSq (u n - v)) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 v) := by
  have hs : Tendsto (fun n => ‖u n - v‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) (fun n =>
      E.sq_norm_le_energyNormSq (E.domain.sub_mem (hu n) hv)) h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have ht := (Real.continuous_sqrt.tendsto 0).comp hs
  simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using ht

theorem coreLimit_iff_mem_killedCoreClosure (E : DirichletForm.ClosedForm m)
    (U : Set X) (u : Lp ℝ 2 m) :
    IsCoreLimitOn E U u ↔ u ∈ E.killedCoreClosure U := by
  constructor
  · rintro ⟨hu, w, hw, hlim⟩
    refine ⟨hu, fun ε hε => ?_⟩
    obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
    exact ⟨w n, hw n, hn⟩
  · intro hu
    exact ⟨hu.1, (E.isKilledDomain_killedCoreClosure U).exists_seq hu⟩

theorem graphClosed_killedCoreClosure (E : DirichletForm.ClosedForm m) (U : Set X) :
    GraphClosed E (E.killedCoreClosure U) := by
  have h := E.isKilledDomain_killedCoreClosure U
  exact ⟨h.le_domain, h.isClosed⟩

theorem zeroOutside_coreLimit (E : DirichletForm.ClosedForm m) (U : Set X)
    (u : Lp ℝ 2 m) (hu : IsCoreLimitOn E U u) : ZeroOutside U u := by
  obtain ⟨hu, w, hw, hlim⟩ := hu
  apply zeroOutside_of_tendsto (u := w)
  · intro n
    obtain ⟨f, _, _, hs, hf⟩ := (hw n).2
    filter_upwards [hf] with x hx hxU
    rw [hx]
    exact image_eq_zero_of_notMem_tsupport (fun h => hxU (hs h))
  · apply tendsto_Lp_of_energy E (fun n => (hw n).1) hu
    refine hlim.congr fun n => ?_
    exact E.energyNormSq_sub_comm hu (hw n).1

end SubdiffusiveProcess.PartProcess
