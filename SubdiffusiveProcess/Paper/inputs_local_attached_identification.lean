module

public import SubdiffusiveProcess.Paper.inputs_classical_e7
public import SubdiffusiveProcess.Paper.inputs_local_compact_coefficients
public import SubdiffusiveProcess.Paper.inputs_local_coefficients_c11
public import SubdiffusiveProcess.Paper.cutoff_lifetime_package
public import SubdiffusiveProcess.Probability.Diffusion.AnalyticBridge

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem inputs_local_attached_identification
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hd : 2 ≤ d) (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N)) (hcross : in_crossing M H PN KN) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      LocalDiffusion (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N)
        (aux_cutoff_lifetime_package_kernel KN N omega) := by
  rcases hcross with ⟨hres, hconservative, hfdd⟩
  filter_upwards [hres, hfdd, inputs_local_coefficients_c11 M H hd hH]
    with omega hresomega hfddomega hregular
  intro N
  obtain ⟨D, hdense, hweak, hlaplace⟩ := hresomega N
  obtain ⟨hc11, hrho11⟩ := hregular N
  let Komega : Kernel (SpatialCoordinates d) (DiffusionPath d) :=
    (KN N).comap (fun x => (omega, x)) (measurable_const.prodMk measurable_id)
  letI : IsMarkovKernel (KN N) := hKN N
  have hKomega : IsMarkovKernel Komega := by
    dsimp [Komega]
    infer_instance
  have hKfdd : ∀ I x, Komega.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x := by
    intro I x
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)]
    change Measure.map (ContinuousPath.finsetEvaluation I) (KN N (omega, x)) = _
    rw [← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)]
    exact hfddomega N I x
  have hcpos := Lane4.cutoffCoefficient_pos M H omega N
  have hrhopos : ∀ x, 0 < cutoffSpeedDensity M H omega N x :=
    fun _ => Real.exp_pos _
  obtain ⟨hrestart, hgen⟩ := inputs_classical_e7 d
    (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N)
    hcpos hrhopos hc11 hrho11 (PN N omega) (hconservative N omega)
    D hdense hweak hlaplace Komega hKomega hKfdd
  refine ⟨SubdiffusiveProcess.Probability.Diffusion.strongMarkov_of_restart hrestart,
    inputs_local_compact_coefficients M H omega N, ?_⟩
  intro U hU hUb s hs f hf
  exact SubdiffusiveProcess.Probability.Diffusion.killedResolvent_clause_of_killedGenerator
    hgen hU hUb
    (SubdiffusiveProcess.Assumptions.CoefficientRegularity.coefficientOn_of_continuous_pos
      (SubdiffusiveProcess.Probability.Diffusion.continuous_of_locallyC11 hc11) hcpos hUb)
    (SubdiffusiveProcess.Assumptions.CoefficientRegularity.coefficientOn_of_continuous_pos
      (SubdiffusiveProcess.Probability.Diffusion.continuous_of_locallyC11 hrho11) hrhopos hUb)
    hs hf

end Paper

