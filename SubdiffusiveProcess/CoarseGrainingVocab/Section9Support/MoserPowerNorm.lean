module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserPowerEnergy
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserCutoffNorm

@[expose] public section

/-! # Norm readout for the arbitrary-power cutoff energy -/
set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Filter Set
open scoped ENNReal Topology
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
variable {d : ℕ} {U : Set (Vec d)}

/-- The square-integral bound controls every coordinate gradient norm. -/
theorem moser_power_cutoff_gradient_l2
    (hU : IsOpenBoundedConvexDomain U) {a : Vec d → ℝ}
    (hameas : AEStronglyMeasurable a (volume.restrict U))
    (habounds : ∀ᵐ x ∂volume.restrict U, 1 / 2 ≤ a x ∧ a x ≤ 2)
    (v u f : H1Function U) (hu : IsWeaklyHarmonicOn a U v)
    {s : ℝ} (hs : 1 ≤ s) (hpair : MoserPowerPair v u f s)
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetac : HasCompactSupport eta) (hetasub : tsupport eta ⊆ U)
    (hetaRange : ∀ x, 0 ≤ eta x ∧ eta x ≤ 1)
    {K : ℝ} (hK : 0 ≤ K)
    (hgrad : ∀ x, vecNormSq (euclideanGradient eta x) ≤ K ^ 2) (i : Fin d) :
    let w := u.mulContDiffHasCompactSupport heta hetac
    eLpNorm (fun x => w.grad x i) 2 (volume.restrict U) ≤
      ENNReal.ofReal (6 * s * K) * eLpNorm u.toFun 2 (volume.restrict U) := by
  have hs0 : 0 ≤ s := by linarith
  let w := u.mulContDiffHasCompactSupport heta hetac
  change eLpNorm (fun x => w.grad x i) 2 (volume.restrict U) ≤ _
  have hB : IntegrableOn
      (fun x => u.toFun x ^ 2 * vecNormSq (euclideanGradient eta x)) U := by
    have hb := WeakPoissonEquationOn.integrableOn_mul_left_of_continuous_hasCompactSupport
      (continuous_vecNormSq_euclideanGradient_of_contDiff heta)
      (hasCompactSupport_vecNormSq_euclideanGradient hetac) u.memL2.integrable_sq
    exact hb.congr_fun (fun x _ => mul_comm _ _) hU.isOpen.measurableSet
  have hBbound :
      ∫ x in U, u.toFun x ^ 2 * vecNormSq (euclideanGradient eta x) ≤
        K ^ 2 * ∫ x in U, u.toFun x ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono_ae hB (u.memL2.integrable_sq.const_mul (K ^ 2))
      (Eventually.of_forall fun x => ?_)
    exact (mul_le_mul_of_nonneg_left (hgrad x) (sq_nonneg _)).trans_eq (mul_comm _ _)
  have henergy := moser_power_cutoff_gradient_energy hU hameas habounds v u f hu hs hpair
    heta hetac hetasub hetaRange
  have hcoord : ∫ x in U, (w.grad x i) ^ 2 ≤ ∫ x in U, vecNormSq (w.grad x) :=
    integral_mono_ae (w.gradMemL2 i).integrable_sq (integrableOn_vecNormSq_h1Grad w)
      (Eventually.of_forall fun x => WeakPoissonEquationOn.coord_sq_le_vecNormSq (w.grad x) i)
  have hcoord' : ∫ x in U, (w.grad x i) ^ 2 ≤
      (34 * s ^ 2) * (K ^ 2 * ∫ x in U, u.toFun x ^ 2) :=
    hcoord.trans (henergy.trans (mul_le_mul_of_nonneg_left hBbound (by positivity)))
  have hsq : (eLpNorm (fun x => w.grad x i) 2 (volume.restrict U)).toReal ^ 2 ≤
      (6 * s * K * (eLpNorm u.toFun 2 (volume.restrict U)).toReal) ^ 2 := by
    rw [← toReal_eLpNorm_two_sq_eq_integral_sq (w.gradMemL2 i),
      ← toReal_eLpNorm_two_sq_eq_integral_sq u.memL2] at hcoord'
    nlinarith [mul_nonneg (sq_nonneg s) (mul_nonneg (sq_nonneg K)
      (sq_nonneg (eLpNorm u.toFun 2 (volume.restrict U)).toReal))]
  have hreal := (sq_le_sq₀ ENNReal.toReal_nonneg (by positivity)).mp hsq
  apply (ENNReal.toReal_le_toReal (w.gradMemL2 i).eLpNorm_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top u.memL2.eLpNorm_ne_top)).mp
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 6 * s * K)]
    using hreal

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
