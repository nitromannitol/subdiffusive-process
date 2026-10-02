import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationPathAlgebra
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationLocalKolmogorov
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationFourthMoment

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open Homogenization hiding Vec contDiff_vecNormSq
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open MeasureTheory ProbabilityTheory MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open scoped ENNReal NNReal

theorem supportedOnContinuousPaths_of_weakResolvent_linearGrowth {d : ℕ} {c rho : Vec d → ℝ}
    (B : MassiveCubeBounds c rho) (hc : ContDiff ℝ 1 c) (hrho : Continuous rho)
    (D : C0ResolventDatum (Vec d)) (hdense : ∀ mu, DenseRange (D.operator mu))
    (hD : IsWeakEllipticResolvent c rho D) (hcnn : ∀ y, 0 ≤ c y)
    (hP : (D.fellerKernelSemigroup hdense).IsConservative)
    {K : ℝ} (hK : 0 ≤ K)
    (hgrowth : ∀ y, euclideanNorm (euclideanGradient c y)+c y ≤ K*rho y*(1+‖y‖)) :
    Kernel.IsSupportedOnContinuousPaths (denseTimeTrajectory (D.fellerKernelSemigroup hdense) hP
      DenseTime.enumeration DenseTime.castOrderEmbedding.toEmbedding) := by
  let C := 8*((d:ℝ)+1)*K
  let Bcap := 4*K
  let K4 := (2*C+8*Bcap)*C
  let D4 := C+(2*C+8*Bcap)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hBcap : 0 ≤ Bcap := by dsimp only [Bcap]; positivity
  have hK4 : 0 ≤ K4 := by dsimp only [K4]; positivity
  have hD4 : 0 ≤ D4 := by dsimp only [D4]; positivity
  apply supportedOnContinuousPaths_of_centeredFourth (D.fellerKernelSemigroup hdense) hP
    (Real.toNNReal K4) (fun t ↦ Real.toNNReal (Real.exp (D4*(t:ℝ))))
    (monotone_toNNReal_exp_mul hD4)
  intro t x
  have hbounds := centered_drift_bounds_of_linearGrowth (hc.differentiable le_rfl)
    hcnn B.weight_pos hK hgrowth x
  have h := lintegral_centered_fourth_le_exp B hc hrho D hdense hD hcnn hP x
    hC hBcap (show 1 ≤ 1+vecNormSq x by linarith [vecNormSq_nonneg x])
    (fun y ↦ (hbounds y).1) (fun y ↦ (hbounds y).2) t
  change _ ≤ ENNReal.ofReal (K4*(1+vecNormSq x)^2*(t:ℝ)^2*Real.exp (D4*(t:ℝ))) at h
  rw [ofReal_fourth_profile hK4 (Real.exp_pos _).le] at h
  exact h

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
