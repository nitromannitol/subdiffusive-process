import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.Packet455DirichletForm

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.Packet455
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledDatumFields
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section
namespace SubdiffusiveProcess.Section10

/-- Restrict an all-H10 Sobolev estimate to the actual killed generator domain.
The Sobolev estimate is a model input, not an asserted classical fact. -/
theorem killed_generator_sobolev_of_h10
    {d : ℕ} {U : Set (Vec d)} {c rho : Vec d → ℝ} {lam Lam : ℝ}
    {law : Kernel (Vec d) (Path d)}
    (hD : LocalDiffusion c rho law) [IsMarkovKernel law]
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)]
    (hEll : IsEllipticFieldOn lam Lam U (SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField c))
    (q : ℝ≥0∞) (K : ℝ)
    (hsob : ∀ u : H10Function U,
      eLpNorm u.toH1Function.toFun q ((weightedMeasure rho).restrict U) ^ (2 : ℕ) ≤
        ENNReal.ofReal K * ENNReal.ofReal (energy c U u.toH1Function))
    (f : (killedSCCS hD hD.1 hU hUb).generatorDomain) :
    eLpNorm ((f : Lp ℝ 2 ((weightedMeasure rho).restrict U)) : Vec d → ℝ)
        q ((weightedMeasure rho).restrict U) ^ (2 : ℕ) ≤
      ENNReal.ofReal K * ENNReal.ofReal
        (-⟪(killedSCCS hD hD.1 hU hUb).generator f, (f : Lp ℝ 2 _)⟫) := by
  obtain ⟨u, hu, hform⟩ := exists_generator_form_identity hD hU hUb hEll f
  have he := hform u (f : Lp ℝ 2 _) hu
  rw [dirichletBilin_self] at he
  rw [eLpNorm_congr_ae hu, ← he]
  exact hsob u



theorem ofReal_energy_eq_lintegral
    {d : ℕ} {U : Set (Vec d)} {c : Vec d → ℝ}
    (hc : CoefficientOn U c) (v : H1Function U) :
    ENNReal.ofReal (energy c U v) =
      ∫⁻ x in U, ENNReal.ofReal (c x * vecDot (v.grad x) (v.grad x)) := by
  have hi := SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledStrongContinuity.integrableOn_energy_pairing
    hc v.grad_memVectorL2 v.grad_memVectorL2
  have hi' : IntegrableOn (fun x => c x * vecDot (v.grad x) (v.grad x)) U := by
    simpa only [vecDot_smul_left] using hi
  obtain ⟨_, lo, _, hlo, hb⟩ := hc
  have hn : ∀ᵐ x ∂(volume.restrict U), 0 ≤ c x * vecDot (v.grad x) (v.grad x) := by
    filter_upwards [hb] with x hx
    exact mul_nonneg (hlo.le.trans hx.1) (vecNormSq_nonneg (v.grad x))
  exact ofReal_integral_eq_lintegral_ofReal hi' hn


end SubdiffusiveProcess.Section10
