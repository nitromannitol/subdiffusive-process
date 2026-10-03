module

public import SubdiffusiveProcess.Paper.aux_lem_tightness_deterministic_restart_jointLaw
public import MarkovProcess.Restart.RestrictedRestartOfJoint

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem aux_lem_tightness_deterministic_restart_restrictedMap
    {alpha : Type*} [TopologicalSpace alpha] [T1Space alpha] [T2Space alpha]
    [MeasurableSpace alpha] [BorelSpace alpha]
    (t : ℝ≥0)
    (mu : Measure (ContinuousPath alpha)) [SFinite mu]
    (past : ContinuousPath alpha → Set.Iic t → alpha)
    (hPast : Measurable past)
    (Q : Kernel alpha (ContinuousPath alpha)) [IsSFiniteKernel Q]
    (terminal : (Set.Iic t → alpha) → alpha) (hTerminal : Measurable terminal)
    (hJoint :
      mu.map (fun path ↦ (past path, ContinuousPath.shift t path)) =
        (mu.map past) ⊗ₘ Q.comap terminal hTerminal) :
    ∀ A : Set (ContinuousPath alpha),
        MeasurableSet[MeasurableSpace.comap past inferInstance] A →
        (mu.restrict A).map (ContinuousPath.shift t) =
          (Q.comap terminal hTerminal).comap past hPast ∘ₘ (mu.restrict A) := by
  intro A hA
  have hShift : Measurable (ContinuousPath.shift t) :=
    ContinuousPath.measurable_shift_fixed (alpha := alpha) t
  exact MarkovProcess.restrict_map_eq_comap_comp_of_map_prodMk_eq_compProd
    mu past hPast (ContinuousPath.shift t) hShift (Q.comap terminal hTerminal) hJoint A hA


end Paper
