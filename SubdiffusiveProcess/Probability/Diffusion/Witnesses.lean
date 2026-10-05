module

public import SubdiffusiveProcess.Probability.Diffusion.Brownian
public import SubdiffusiveProcess.Probability.Diffusion.AnalyticBridge

@[expose] public section




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open _root_.SubdiffusiveProcess.Model
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion

variable {d : ℕ}

/-- The constructed Brownian law gives the full constant-coefficient witness once
its killed-generator identification and continuous killed densities are proved. -/
theorem localDiffusionData_laplacianLaw_of_analyticInput
    (hgen : Input.KilledGenerator (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) (laplacianLaw d))
    (hdens : Input.ContinuousKilledDensities (fun _ => (1 : ℝ)) (laplacianLaw d)) :
    LocalDiffusionData (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) (laplacianLaw d) :=
  localDiffusionData_of_killedGenerator strongMarkov_laplacianLaw
    continuous_const (fun _ => one_pos) continuous_const (fun _ => one_pos) hgen hdens

/-- T1, explicitly conditional on the two remaining analytic inputs for the concrete law. -/
theorem exists_localDiffusionData_const_of_analyticInput (d : ℕ)
    (hgen : Input.KilledGenerator (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) (laplacianLaw d))
    (hdens : Input.ContinuousKilledDensities (fun _ => (1 : ℝ)) (laplacianLaw d)) :
    ∃ law : Kernel (Vec d) (Path d), LocalDiffusionData (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) law :=
  ⟨laplacianLaw d, localDiffusionData_laplacianLaw_of_analyticInput hgen hdens⟩

/-- The primitive local regularity interface is equivalent to the formalization predicate on `univ`. -/
theorem locallyC11_iff_coefficientC11On_univ (a : Vec d → ℝ) :
    Input.LocallyC11 a ↔ CoefficientC11On univ a := by
  constructor
  · rintro ⟨Da, hDa, hLip⟩
    exact ⟨Da, fun x _ => hDa x, fun K hK _ => hLip K hK⟩
  · rintro ⟨Da, hDa, hLip⟩
    exact ⟨Da, fun x => hDa x (mem_univ x), fun K hK => hLip K hK (subset_univ K)⟩

/-- Every anchored `C¹ˑ¹` sample supplies the primitive regularity input. -/
theorem locallyC11_aAnchored (M : GMCModel d) (omega : AnchoredC11Sample d) :
    Input.LocallyC11 (aAnchored M omega) :=
  (locallyC11_iff_coefficientC11On_univ _).mpr
    (_root_.SubdiffusiveProcess.Model.coefficientC11On_aAnchored M omega univ)

/-- T3: the weighted anchored diffusion follows from the explicit smooth realization theorem. -/
theorem exists_localDiffusionData_aAnchored_weighted_of_smoothRealization
    (hrealize : Input.SmoothRealization d) (M : GMCModel d) (omega : AnchoredC11Sample d) :
    ∃ law : Kernel (Vec d) (Path d),
      LocalDiffusionData (aAnchored M omega) (aAnchored M omega) law :=
  exists_localDiffusionData_of_smoothRealization hrealize (aAnchored M omega)
    (aAnchored_pos M omega) (locallyC11_aAnchored M omega) _ (Or.inl rfl)

/-- T3: the divergence-form anchored diffusion follows from the same realization theorem.
The conclusion permits finite lifetime; no a.e. growth condition is silently imposed. -/
theorem exists_localDiffusionData_aAnchored_divergence_of_smoothRealization
    (hrealize : Input.SmoothRealization d) (M : GMCModel d) (omega : AnchoredC11Sample d) :
    ∃ law : Kernel (Vec d) (Path d),
      LocalDiffusionData (aAnchored M omega) (fun _ => (1 : ℝ)) law :=
  exists_localDiffusionData_of_smoothRealization hrealize (aAnchored M omega)
    (aAnchored_pos M omega) (locallyC11_aAnchored M omega) _ (Or.inr rfl)

end SubdiffusiveProcess.Probability.Diffusion
