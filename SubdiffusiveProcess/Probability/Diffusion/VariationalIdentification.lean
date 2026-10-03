module

public import SubdiffusiveProcess.Probability.Diffusion.VariationalResolvent
public import SubdiffusiveProcess.Probability.Diffusion.Witnesses

@[expose] public section




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal NNReal BigOperators Topology

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion

variable {d : ℕ}

/-- The established Sobolev representative carries the literal approximation
data demanded by the primitive input. -/
def boundaryApproximationOfH10 {U : Set (Vec d)} (u : H10Function U) :
    Input.BoundaryApproximation U u.toH1Function.toFun u.toH1Function.grad where
  memLp := u.toH1Function.memL2
  grad_memLp := u.toH1Function.gradMemL2
  approx := u.approx
  smooth := u.approx_smooth
  compactSupport := u.approx_hasCompactSupport
  support_subset := u.approx_support_subset
  tendsto_fun := u.tendsto_approx
  tendsto_grad := u.tendsto_approx_grad

/-- Exact unresolved identification of the Brownian part with the variational
Dirichlet Laplacian, quantified over every bounded open set. -/
def BrownianVariationalIdentification (d : ℕ) : Prop :=
  ∀ U : Set (Vec d), ∀ hU : IsOpen U, Bornology.IsBounded U →
    ∀ s : ℝ, ∀ hs : 0 < s, ∀ f : Vec d → ℝ,
      ∀ hf : MemLp f 2 (volume.restrict U),
        (variationalResolvent hU hs hf).toH1Function.toFun =ᵐ[volume.restrict U]
          killedResolvent (laplacianLaw d) U s f

/-- The killed occupation integral respects the Lebesgue `L²` class without a
weak PDE premise. -/
theorem killedResolvent_laplacianLaw_congr_ae {U : Set (Vec d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {s : ℝ} (hs : 0 < s) {f g : Vec d → ℝ}
    (hfg : f =ᵐ[volume.restrict U] g)
    (hf : MemLp f 2 (volume.restrict U)) (hg : MemLp g 2 (volume.restrict U)) :
    killedResolvent (laplacianLaw d) U s f =ᵐ[volume.restrict U]
      killedResolvent (laplacianLaw d) U s g := by
  letI := SubdiffusiveProcess.Model.isFiniteMeasure_volume_restrict hUb
  have hsub := resolventKernel_laplacianLaw_subinvariant U hU s hs
  have e1 := resolventKernel_integral_ae (laplacianLaw d) U hU s hs _ hsub f
    (hf.integrable (by norm_num))
  have e2 := resolventKernel_integral_ae (laplacianLaw d) U hU s hs _ hsub g
    (hg.integrable (by norm_num))
  exact e1.symm.trans ((kernelIntegral_congr_ae hsub hfg).trans e2)

/-- The actual `L²` operator represents the raw resolvent of every `L²` datum. -/
theorem laplacianResolventLp_toLp_coeFn {U : Set (Vec d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {s : ℝ} (hs : 0 < s) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) :
    laplacianResolventLp U hU hUb s hs (hf.toLp f) =ᵐ[volume.restrict U]
      killedResolvent (laplacianLaw d) U s f :=
  (laplacianResolventLp_coeFn U hU hUb s hs (hf.toLp f)).trans
    (killedResolvent_laplacianLaw_congr_ae hU hUb hs hf.coeFn_toLp (Lp.memLp _) hf)

/-- The missing part-form equality implies the complete primitive killed-generator
target, including compact-support approximation and the normalized test equation. -/
theorem killedGenerator_laplacianLaw_of_variationalIdentification
    (hpart : BrownianVariationalIdentification d) :
    Input.KilledGenerator (fun _ => 1) (fun _ => 1) (laplacianLaw d) := by
  intro U hU hUb s hs f hf
  have hfvol : MemLp f 2 (volume.restrict U) := by
    simpa only [Input.speedMeasure, ENNReal.ofReal_one, withDensity_const, one_smul] using hf
  let u := variationalResolvent hU hs hfvol
  refine ⟨u.toH1Function.toFun, u.toH1Function.grad,
    ⟨boundaryApproximationOfH10 u⟩, ?_, ?_⟩
  · simpa only [Input.speedMeasure, ENNReal.ofReal_one, withDensity_const, one_smul] using!
      hpart U hU hUb s hs f hfvol
  · intro ψ hψ hcompact hsupp
    let φ := H10Function.ofContDiff hU hψ hcompact hsupp
    have hu := variationalResolvent_spec hU hs hfvol φ
    have huf : IntegrableOn (fun x => u.toH1Function.toFun x * ψ x) U := by
      simpa only [one_mul, φ, H10Function.ofContDiff] using! integrableOn_mass_term
        (rho := fun _ => 1) aestronglyMeasurable_const
        (Eventually.of_forall fun _ => (show |(1 : ℝ)| ≤ 1 by norm_num))
        u.toH1Function.memL2 φ.toH1Function.memL2
    have hff : IntegrableOn (fun x => f x * ψ x) U := by
      simpa only [one_mul, φ, H10Function.ofContDiff] using! integrableOn_mass_term
        (rho := fun _ => 1) aestronglyMeasurable_const
        (Eventually.of_forall fun _ => (show |(1 : ℝ)| ≤ 1 by norm_num))
        hfvol φ.toH1Function.memL2
    have hsplit : (∫ x in U, (1 * (s⁻¹ * (f x - u.toH1Function.toFun x))) * ψ x) =
        s⁻¹ * (∫ x in U, f x * ψ x) -
          s⁻¹ * (∫ x in U, u.toH1Function.toFun x * ψ x) := by
      rw [← integral_const_mul, ← integral_const_mul,
        ← integral_sub (hff.const_mul s⁻¹) (huf.const_mul s⁻¹)]
      exact integral_congr_ae (Eventually.of_forall fun _ => by ring)
    rw [hsplit]
    have hrhs : (∫ x in U, 1 * (s⁻¹ * f x) * ψ x) =
        s⁻¹ * (∫ x in U, f x * ψ x) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun _ => by ring)
    change s⁻¹ * (∫ x in U, 1 * u.toH1Function.toFun x * ψ x) +
      (∫ x in U, ∑ i, (1 * u.toH1Function.grad x i) *
        (fderiv ℝ ψ x) (Pi.single i 1)) =
          (∫ x in U, 1 * (s⁻¹ * f x) * ψ x) at hu
    rw [hrhs] at hu
    simp only [one_mul] at hu ⊢
    linarith

/-- The unresolved equality is exactly the remaining target. This reverse
direction uses variational uniqueness; it does not assert the equality. -/
theorem killedGenerator_laplacianLaw_iff_variationalIdentification :
    Input.KilledGenerator (fun _ => 1) (fun _ => 1) (laplacianLaw d) ↔
      BrownianVariationalIdentification d := by
  constructor
  · intro hgen U hU hUb s hs f hf
    have hfw : MemLp f 2 ((weightedMeasure (fun _ => 1)).restrict U) := by
      simpa only [weightedMeasure, ENNReal.ofReal_one, withDensity_const, one_smul] using hf
    obtain ⟨u, hae, hsol⟩ := killedResolvent_clause_of_killedGenerator hgen hU hUb
      (SubdiffusiveProcess.Model.LifetimeProcess.coefficientOn_one U)
      (SubdiffusiveProcess.Model.LifetimeProcess.coefficientOn_one U) hs hfw
    have hae' : u.toH1Function.toFun =ᵐ[volume.restrict U]
        killedResolvent (laplacianLaw d) U s f := by
      simpa only [weightedMeasure, ENNReal.ofReal_one, withDensity_const, one_smul] using hae
    exact (variationalResolvent_unique hU hs hf u hsol).1.symm.trans hae'
  · exact killedGenerator_laplacianLaw_of_variationalIdentification

/-- The exact constant-coefficient diffusion follows from the two remaining
analytic theorems, with its variational half now fully constructed. -/
theorem localDiffusionData_laplacianLaw_of_variationalIdentification
    (hpart : BrownianVariationalIdentification d)
    (hdens : Input.ContinuousKilledDensities (fun _ => 1) (laplacianLaw d)) :
    LocalDiffusionData (fun _ => 1) (fun _ => 1) (laplacianLaw d) :=
  localDiffusionData_laplacianLaw_of_analyticInput
    (killedGenerator_laplacianLaw_of_variationalIdentification hpart) hdens

end SubdiffusiveProcess.Probability.Diffusion
