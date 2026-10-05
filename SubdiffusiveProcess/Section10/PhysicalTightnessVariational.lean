module

public import SubdiffusiveProcess.Section10.PhysicalTightnessResolvent
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.CommonFormOnH1Function
public import SubdiffusiveProcess.CoarseGrainingVocab.Section11.SubunitEstimates

@[expose] public section

/-! Deterministic ingredients of §8 Step 1, factored from `tight_fast_exit`.
All lemmas retain the actual weak-resolvent equation and scalar weighted energy.
No variational conclusion is supplied as a new diffusion-structure field. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra
open _root_.SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.CommonFormOnH1Function
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledDensityExistence
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section11
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness

theorem weighted_lintegral {d : ℕ}
    {U : Set (Homogenization.Vec d)} (hU : MeasurableSet U)
    {b g : Homogenization.Vec d → ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict U))
    (hg : AEStronglyMeasurable g (volume.restrict U))
    (hb0 : ∀ᵐ x ∂volume.restrict U, 0 ≤ b x)
    (hg0 : ∀ᵐ x ∂volume.restrict U, 0 ≤ g x)
    (hi : Integrable (fun x => b x * g x) (volume.restrict U)) :
    (∫⁻ x in U, ENNReal.ofReal (g x * b x) ∂volume) =
      ENNReal.ofReal (∫ x in U, b x * g x ∂volume) := by
  have h := weighted_lintegral_ofReal_eq hU hb hg hb0 hg0 hi
  unfold weightedMeasure at h
  rw [restrict_withDensity hU,
    lintegral_withDensity_eq_lintegral_mul₀ hb.aemeasurable.ennreal_ofReal
      hg.aemeasurable.ennreal_ofReal] at h
  rw [← h]
  apply lintegral_congr_ae
  filter_upwards [hb0] with x hx
  change ENNReal.ofReal (g x * b x) =
    ENNReal.ofReal (b x) * ENNReal.ofReal (g x)
  rw [mul_comm, ENNReal.ofReal_mul hx]

theorem resolvent_bounds {d : ℕ}
    (law : Kernel (Homogenization.Vec d) (Path d)) [IsMarkovKernel law]
    (U : Set (Homogenization.Vec d)) (hU : IsOpen U) (s : ℝ) (hs : 0 < s)
    (f : Homogenization.Vec d → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (x : Homogenization.Vec d) :
    0 ≤ killedResolvent law U s f x ∧ killedResolvent law U s f x ≤ 1 := by
  let R := resolventKernel law U hU s hs
  let : IsSubMarkovKernel R := resolventKernel_subMarkov law U hU s hs
  let : IsFiniteKernel R := (resolventKernel_subMarkov law U hU s hs).isFiniteKernel
  have hfi : Integrable f (R x) :=
    Integrable.of_bound hf.aestronglyMeasurable 1
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 z)]
        exact hf1 z)
  rw [← resolventKernel_integral_eq_of_integrable law U hU s hs f x hfi]
  change 0 ≤ (∫ z, f z ∂(R x)) ∧ (∫ z, f z ∂(R x)) ≤ 1
  refine ⟨integral_nonneg hf0, ?_⟩
  calc
    (∫ z, f z ∂(R x)) ≤ ∫ _z, (1 : ℝ) ∂(R x) :=
      integral_mono hfi (integrable_const 1) hf1
    _ = (R x Set.univ).toReal := by
      simp only [integral_const, smul_eq_mul, mul_one, measureReal_def]
    _ ≤ 1 := by
      exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2
        ((resolventKernel_subMarkov law U hU s hs).measure_le_one x Set.univ)

theorem weak_resolvent {d : ℕ}
    {c rho : Homogenization.Vec d → ℝ} {law : Kernel (Homogenization.Vec d) (Path d)}
    [IsMarkovKernel law] (hD : LocalDiffusion c rho law) (U : Set (Homogenization.Vec d))
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (s : ℝ) (hs : 0 < s)
    (f : Homogenization.Vec d → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hf2 : MemLp f 2 ((weightedMeasure rho).restrict U)) :
    ∃ u : H10Function U,
      u.toFun =ᵐ[(weightedMeasure rho).restrict U] killedResolvent law U s f ∧
      IsMassiveWeakSolutionOn c rho s⁻¹ U u.toH1Function (fun x => s⁻¹ * f x) ∧
      ∀ᵐ x ∂(weightedMeasure rho).restrict U, 0 ≤ u.toFun x ∧ u.toFun x ≤ 1 := by
  obtain ⟨u, hueq, hu⟩ := hD.2.2 U hU hUb s hs f hf2
  refine ⟨u, hueq, hu, ?_⟩
  filter_upwards [hueq] with x hx
  rw [hx]
  exact resolvent_bounds law U hU s hs f hf hf0 hf1 x

theorem variational_algebra {r s eu euv ev : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hu : 0 ≤ eu)
    (hdiff : 0 ≤ eu - 2 * euv + ev)
    (heq : r + s * (eu - euv) = 0) : r ≤ s * ev := by
  have h1 := mul_nonneg hs hdiff
  have h2 := mul_nonneg hs hu
  nlinarith only [hr, heq, h1, h2]

theorem variational_comparison {d : ℕ}
    {U : Set (SubdiffusiveProcess.CoarseGrainingVocab.Vec d)}
    {c rho : SubdiffusiveProcess.CoarseGrainingVocab.Vec d → ℝ} {lam Lam rhoMax s : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U (scalarCoeffField c))
    (hc : ∀ᵐ x ∂volume.restrict U, 0 ≤ c x)
    (hrho : ∀ᵐ x ∂volume.restrict U, 0 ≤ rho x)
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict U))
    (hrhoBdd : ∀ᵐ x ∂volume.restrict U, |rho x| ≤ rhoMax)
    (hs : 0 < s) (u eta : H10Function U)
    (hu : IsMassiveWeakSolutionOn c rho s⁻¹ U u.toH1Function
      (fun x => s⁻¹ * eta.toFun x)) :
    (∫ x in U, rho x * (u.toFun x - eta.toFun x) ^ 2) ≤
      s * energy c U eta.toH1Function := by
  let v := u.toH1Function
  let e := eta.toH1Function
  let r := ∫ x in U, rho x * (u.toFun x - eta.toFun x) ^ 2
  have hfun : (u - eta).toH1Function.toFun = fun x => u.toFun x - eta.toFun x := by
    change (u.toH1Function - eta.toH1Function).toFun = _
    exact H1Function.sub_toFun _ _
  have htest := resolvent_form_identity hEll hs hu (u - eta)
  have hi1 := integrableOn_mass_term hrhoMeas hrhoBdd
    u.toH1Function.memL2 (u - eta).toH1Function.memL2
  have hi2 := integrableOn_mass_term hrhoMeas hrhoBdd
    eta.toH1Function.memL2 (u - eta).toH1Function.memL2
  have hmass :
      (∫ x in U, rho x * u.toFun x * (u - eta).toH1Function.toFun x) -
        (∫ x in U, rho x * eta.toFun x * (u - eta).toH1Function.toFun x) = r := by
    rw [← integral_sub hi1 hi2]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    rw [hfun]
    ring
  have hgrad : (u - eta).toH1Function = v - e := rfl
  have htest' : r + s * (dirichletBilin hEll v v - dirichletBilin hEll v e) = 0 := by
    rw [hgrad, map_sub] at htest
    rw [H1Function.sub_toFun] at htest
    rw [hfun] at hmass
    dsimp only [v, e] at *
    linarith only [htest, hmass]
  have hr : 0 ≤ r := by
    apply integral_nonneg_of_ae
    filter_upwards [hrho] with x hx
    exact mul_nonneg hx (sq_nonneg _)
  have hpos : ∀ w : H1Function U, 0 ≤ dirichletBilin hEll w w := by
    intro w
    rw [dirichletBilin_apply]
    apply integral_nonneg_of_ae
    filter_upwards [hc] with x hx
    exact mul_nonneg hx
      (SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledResolventLp.vecDot_self_nonneg _)
  have hdiff := hpos (v - e)
  simp only [map_sub, LinearMap.sub_apply] at hdiff
  rw [dirichletBilin_symm hEll e v] at hdiff
  have hdiff' : 0 ≤ dirichletBilin hEll v v - 2 * dirichletBilin hEll v e +
      dirichletBilin hEll e e := by linarith only [hdiff]
  have hbound := variational_algebra hr hs.le (hpos v) hdiff' htest'
  simpa only [dirichletBilin_self] using hbound

theorem complement_subsolution {d : ℕ}
    {U : Set (Homogenization.Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]
    {c rho : Homogenization.Vec d → ℝ} {rhoMax mu : ℝ}
    (hmu : 0 ≤ mu)
    (hrho : ∀ᵐ x ∂volume.restrict U, 0 ≤ rho x)
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict U))
    (hrhoBdd : ∀ᵐ x ∂volume.restrict U, |rho x| ≤ rhoMax)
    (u : H1Function U)
    (hu : IsMassiveWeakSolutionOn c rho mu U u (fun _ => mu))
    (hu1 : ∀ᵐ x ∂volume.restrict U, u.toFun x ≤ 1) :
    IsWeakSubSolutionOn c U (H1Function.const 1 - u) := by
  intro psi hpsi
  have hi1 := integrableOn_mass_term hrhoMeas hrhoBdd u.memL2 psi.toH1Function.memL2
  have hi2 := integrableOn_mass_term hrhoMeas hrhoBdd
    (H1Function.const (U := U) 1).memL2 psi.toH1Function.memL2
  have hmass : (∫ x in U, rho x * u.toFun x * psi.toH1Function.toFun x) ≤
      ∫ x in U, rho x * 1 * psi.toH1Function.toFun x := by
    apply integral_mono_ae hi1 hi2
    filter_upwards [hrho, hu1] with x hx hx1
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx1 hx) (hpsi x)
  have htest := hu psi
  have hrhs : (∫ x in U, rho x * mu * psi.toH1Function.toFun x) =
      mu * ∫ x in U, rho x * 1 * psi.toH1Function.toFun x := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hrhs] at htest
  have henergy : 0 ≤ ∫ x in U,
      vecDot (c x • u.grad x) (psi.toH1Function.grad x) := by
    have h := mul_le_mul_of_nonneg_left hmass hmu
    linarith only [htest, h]
  have hgrad : (H1Function.const (U := U) 1 - u).grad = fun x => -u.grad x := by
    rw [H1Function.sub_grad]
    funext x
    change (0 : SubdiffusiveProcess.CoarseGrainingVocab.Vec d) - u.grad x = -u.grad x
    exact zero_sub _
  rw [hgrad]
  have heq : (∫ x in U,
      vecDot (c x • -u.grad x) (psi.toH1Function.grad x)) =
      -(∫ x in U, vecDot (c x • u.grad x) (psi.toH1Function.grad x)) := by
    rw [← integral_neg]
    congr 1
    funext x
    simp only [smul_neg, vecDot_neg_left]
  rw [heq]
  exact neg_nonpos.mpr henergy

theorem source_ae {d : ℕ}
    {U : Set (Homogenization.Vec d)} {c rho : Homogenization.Vec d → ℝ}
    {mu : ℝ} {u : Homogenization.H1Function U}
    {f g : Homogenization.Vec d → ℝ}
    (hfg : f =ᵐ[volume.restrict U] g)
    (hu : IsMassiveWeakSolutionOn c rho mu U u f) :
    IsMassiveWeakSolutionOn c rho mu U u g := by
  intro phi
  have h := hu phi
  have hsrc : (∫ x in U, rho x * f x * phi.toH1Function.toFun x) =
      ∫ x in U, rho x * g x * phi.toH1Function.toFun x := by
    apply integral_congr_ae
    filter_upwards [hfg] with x hx
    rw [hx]
  rw [hsrc] at h
  exact h

end SubdiffusiveProcess.Section10.PhysicalTightness
