import SubdiffusiveProcess.Paper.aux_lem_tightness_deterministic_restart_restrictedMap
import MarkovProcess.Restart.RestrictedRestartOfJoint

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem aux_lem_tightness_deterministic_restart_lintegral_identity
    {alpha : Type*} [TopologicalSpace alpha] [T1Space alpha] [T2Space alpha]
    [MeasurableSpace alpha] [BorelSpace alpha]
    (t : ℝ≥0)
    (mu : Measure (ContinuousPath alpha)) [SFinite mu]
    (past : ContinuousPath alpha → Set.Iic t → alpha)
    (hPast : Measurable past)
    (Q : Kernel alpha (ContinuousPath alpha)) [IsSFiniteKernel Q]
    (terminal : (Set.Iic t → alpha) → alpha) (hTerminal : Measurable terminal)
    (hTerminalPath : terminal ∘ past = fun path ↦ path t)
    (hRestricted : ∀ A : Set (ContinuousPath alpha),
      MeasurableSet[MeasurableSpace.comap past inferInstance] A →
        (mu.restrict A).map (ContinuousPath.shift t) =
          (Q.comap terminal hTerminal).comap past hPast ∘ₘ
            (mu.restrict A)) :
    ∀ A : Set (ContinuousPath alpha),
      MeasurableSet[MeasurableSpace.comap past inferInstance] A →
      ∀ F : ContinuousPath alpha → ℝ≥0∞, Measurable F →
        (∫⁻ path in A, F (ContinuousPath.shift t path) ∂mu) =
          (∫⁻ path in A,
            ∫⁻ future, F future ∂(Q (path t)) ∂mu) := by
  intro A hA F hF
  have hmap := hRestricted A hA
  calc
    (∫⁻ path in A, F (ContinuousPath.shift t path) ∂mu) =
        ∫⁻ path, F path ∂((mu.restrict A).map (ContinuousPath.shift t)) := by
      rw [MeasureTheory.lintegral_map hF
        (ContinuousPath.measurable_shift_fixed (alpha := alpha) t)]
    _ = ∫⁻ path, F path ∂(
        (Q.comap terminal hTerminal).comap past hPast ∘ₘ (mu.restrict A)) := by
      rw [hmap]
    _ = ∫⁻ path,
        ∫⁻ future, F future ∂((Q.comap terminal hTerminal).comap past hPast path)
        ∂(mu.restrict A) := by
      rw [Measure.lintegral_bind
        (Kernel.aemeasurable ((Q.comap terminal hTerminal).comap past hPast))
        hF.aemeasurable]
    _ = ∫⁻ path in A,
        ∫⁻ future, F future ∂(Q (path t)) ∂mu := by
      simp only [Kernel.comap_apply]
      have hterminal : ∀ path : ContinuousPath alpha,
          terminal (past path) = path t := by
        intro path
        exact congrFun hTerminalPath path
      simp_rw [hterminal]

end Paper
