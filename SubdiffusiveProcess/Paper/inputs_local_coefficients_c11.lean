module

public import SubdiffusiveProcess.Paper.finiteDimensional_cutoff_path_kernel
public import SubdiffusiveProcess.Assumptions.AnchoredCoefficientC11
public import SubdiffusiveProcess.Probability.Diffusion.AnalyticInput

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem inputs_local_coefficients_c11
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hd : 2 ≤ d) (hH : InfraredCharacterization M H) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      SubdiffusiveProcess.Probability.Diffusion.Input.LocallyC11 (cutoffCoefficient M H omega N) ∧
        SubdiffusiveProcess.Probability.Diffusion.Input.LocallyC11 (cutoffSpeedDensity M H omega N) := by
  filter_upwards [aux_finiteDimensional_cutoff_path_kernel_potential hd M H hH]
    with omega homega
  intro N
  obtain ⟨g, hg⟩ := homega N
  have hexp : ∀ b : ℝ, SubdiffusiveProcess.Probability.Diffusion.Input.LocallyC11
      (fun x => Real.exp (g x - b)) := by
    intro b
    let q : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d :=
      ⟨(⟨fun x => g x - b, g.1.1.continuous.sub continuous_const⟩, g.deriv),
        (fun x => (g.hasFDerivAt x).sub_const b), g.property.2⟩
    obtain ⟨Dq, hDq, hLip⟩ :=
      SubdiffusiveProcess.Assumptions.AnchoredCoefficientC11.coefficientC11On_exp q Set.univ
    exact ⟨Dq, fun x => hDq x (Set.mem_univ x),
      fun K hK => hLip K hK (Set.subset_univ K)⟩
  let b : ℝ := (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P
  have hspeed : cutoffSpeedDensity M H omega N = fun x => Real.exp (g x - b) := by
    funext x
    exact congrArg (fun v : ℝ => Real.exp (v - b)) (hg x)
  have hcoef : cutoffCoefficient M H omega N =
      fun x => Real.exp (g x - (b + Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N))) := by
    funext x
    unfold cutoffCoefficient
    rw [hg x, sub_add_eq_sub_sub,
      Real.exp_sub (g x - b) (Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)),
      Real.exp_log (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)]
    exact mul_comm _ _
  rw [hcoef, hspeed]
  exact ⟨hexp _, hexp _⟩

end Paper

