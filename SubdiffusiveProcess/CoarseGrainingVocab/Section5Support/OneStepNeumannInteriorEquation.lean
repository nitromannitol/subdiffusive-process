module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepShellJacobianMeasurability
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.HarmonicInteriorHessian
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.LimitHessianPointwise
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.SmoothTestBoundEstimate

@[expose] public section




open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- A mean-zero Neumann solution with `-G` vector datum solves the scalar
interior equation with RHS `div G`. -/
theorem weakPoissonEquationOn_of_isMeanZeroNeumannRhsWeakSolution_neg
    {d : ℕ} (Q : TriadicCube d) (G : CubeVectorH1Function Q)
    (u : H1MeanZeroFunction (openCubeSet Q))
    (hu : IsMeanZeroNeumannRhsWeakSolution
      (identityCoeffField d) (openCubeSet Q) u (fun x => -G.toField x)) :
    WeakPoissonEquationOn (openCubeSet Q) u.toH1Function G.divergence := by
  intro phi hphi hphiSupport hphiSub
  let phi0 : H10Function (openCubeSet Q) :=
    H10Function.ofContDiff (isOpen_openCubeSet Q)
      (hphi.of_le (by simp)) hphiSupport hphiSub
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let phiMean : H1MeanZeroFunction (openCubeSet Q) :=
    phi0.toH1Function.toMeanZero
  have hweak := hu phiMean
  have hparts := G.integral_divergence_mul_zeroTrace_eq_neg_integral_vecDot phi0
  have hleft :
      ∫ x in openCubeSet Q,
          vecDot (u.toH1Function.grad x) (euclideanGradient phi x) ∂volume =
        ∫ x in openCubeSet Q,
          vecDot (u.toH1Function.grad x)
            (phiMean.toH1Function.grad x) ∂volume := by
    apply integral_congr_ae
    filter_upwards with x
    congr 1
    funext i
    simp only [phiMean, H1Function.toMeanZero_grad]
    rfl
  have hright :
      ∫ x in openCubeSet Q, G.divergence x * phi x ∂volume =
        ∫ x in openCubeSet Q,
          G.divergence x * phi0.toH1Function x ∂volume := by
    apply integral_congr_ae
    filter_upwards with x
    simp [phi0, H10Function.ofContDiff, H1Function.ofContDiff]
  calc
    ∫ x in openCubeSet Q,
        vecDot (u.toH1Function.grad x) (euclideanGradient phi x) ∂volume =
      ∫ x in openCubeSet Q,
        vecDot (u.toH1Function.grad x)
          (phiMean.toH1Function.grad x) ∂volume := hleft
    _ = ∫ x in openCubeSet Q,
        vecDot (-G.toField x) (phiMean.toH1Function.grad x) ∂volume := by
      simpa only [matVecMul_identityCoeffField] using hweak
    _ = -∫ x in openCubeSet Q,
        vecDot (G.toField x) (phi0.toH1Function.grad x) ∂volume := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with x
      simp only [vecDot_neg_left, H1Function.toMeanZero_grad, phiMean]
    _ = ∫ x in openCubeSet Q,
        G.divergence x * phi0.toH1Function x ∂volume := hparts.symm
    _ = ∫ x in openCubeSet Q, G.divergence x * phi x ∂volume := hright.symm

/-- Literal specialization to the one-step shell datum. -/
theorem weakPoissonEquationOn_oneStepShellNeumann
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p : Vec d)
    (Q : TriadicCube d) (hh : 0 < h)
    (u : H1MeanZeroFunction (openCubeSet Q))
    (hu : IsMeanZeroNeumannRhsWeakSolution
      (identityCoeffField d) (openCubeSet Q) u
      (fun x => -(oneStepShellForcingH1 M n h omega p Q hh).toField x)) :
    WeakPoissonEquationOn (openCubeSet Q) u.toH1Function
      (oneStepShellForcingH1 M n h omega p Q hh).divergence := by
  exact weakPoissonEquationOn_of_isMeanZeroNeumannRhsWeakSolution_neg Q
    (oneStepShellForcingH1 M n h omega p Q hh) u hu

/-- The library's interior difference-quotient construction applied to the
literal one-step Neumann corrector.  This is the samplewise weak-Hessian
package behind the Neumann `B_z` observable; all constants remain in the
library's explicit smooth-test bound so downstream normalization can be
performed without strengthening the Calderon--Zygmund input. -/
theorem exists_oneStepShellNeumann_innerWeakHessian
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p : Vec d)
    (Q : TriadicCube d) (hh : 0 < h)
    (u : H1MeanZeroFunction (openCubeSet Q))
    (hu : IsMeanZeroNeumannRhsWeakSolution
      (identityCoeffField d) (openCubeSet Q) u
      (fun x => -(oneStepShellForcingH1 M n h omega p Q hh).toField x))
    {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    {rho1 rho2 sigma1 sigma2 nu : ℝ}
    (eta : QuantitativeCubeCutoff Q rho1 rho2)
    (hetaSub : tsupport (eta : Vec d → ℝ) ⊆ V)
    (hinnerV : scaledClosedCubeSet Q rho1 ⊆ V)
    (theta : QuantitativeCubeCutoff Q sigma1 sigma2)
    (hVnu : V ⊆ scaledClosedCubeSet Q nu)
    (hnuNonneg : 0 ≤ nu) (hnuSigma : nu < sigma1)
    (hsigmaOne : sigma1 < 1)
    (hsigmaTwoNonneg : 0 ≤ sigma2) (hsigmaTwo : sigma2 < 1)
    (hrhoNonneg : 0 ≤ rho1) :
    ∃ uS : H1Function (scaledOpenCubeSet Q rho1),
      uS.toFun = u.toH1Function.toFun ∧
        uS.grad = u.toH1Function.grad ∧
          ∃ H : HasWeakHessianOn (scaledOpenCubeSet Q rho1) uS,
            H.hessianCoordL2NormSum ≤
              ∑ i : Fin d, ∑ _j : Fin d,
                WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestBound
                  (ρ₁ := rho1) (ρ₂ := rho2) u.toH1Function
                    (oneStepShellForcingH1 M n h omega p Q hh).divergence
                    i theta := by
  exact
    WeakPoissonEquationOn.exists_hasWeakHessianOn_restrict_hessianCoordL2NormSum_le_of_strict_inner_margin
        (weakPoissonEquationOn_oneStepShellNeumann M n h omega p Q hh u hu)
        (CubeVectorH1Function.divergence_memScalarL2_openCubeSet
          (oneStepShellForcingH1 M n h omega p Q hh))
        hV eta hetaSub hinnerV theta hVnu hnuNonneg hnuSigma hsigmaOne
        hsigmaTwoNonneg hsigmaTwo hrhoNonneg

/-- Reduced-energy form of `exists_oneStepShellNeumann_innerWeakHessian`.
The cutoff factors have been eliminated in favor of unweighted gradient,
value, and divergence integrals, which are the three quantities entering the
cell-moment aggregation. -/
theorem exists_oneStepShellNeumann_innerWeakHessian_reduced
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p : Vec d)
    (Q : TriadicCube d) (hh : 0 < h)
    (u : H1MeanZeroFunction (openCubeSet Q))
    (hu : IsMeanZeroNeumannRhsWeakSolution
      (identityCoeffField d) (openCubeSet Q) u
      (fun x => -(oneStepShellForcingH1 M n h omega p Q hh).toField x))
    {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    {rho1 rho2 sigma1 sigma2 nu : ℝ}
    (eta : QuantitativeCubeCutoff Q rho1 rho2)
    (hetaSub : tsupport (eta : Vec d → ℝ) ⊆ V)
    (hinnerV : scaledClosedCubeSet Q rho1 ⊆ V)
    (theta : QuantitativeCubeCutoff Q sigma1 sigma2)
    (hVnu : V ⊆ scaledClosedCubeSet Q nu)
    (hnuNonneg : 0 ≤ nu) (hnuSigma : nu < sigma1)
    (hsigmaOne : sigma1 < 1)
    (hsigmaTwoNonneg : 0 ≤ sigma2) (hsigmaTwo : sigma2 < 1)
    (hrhoNonneg : 0 ≤ rho1) :
    ∃ uS : H1Function (scaledOpenCubeSet Q rho1),
      uS.toFun = u.toH1Function.toFun ∧
        uS.grad = u.toH1Function.grad ∧
          ∃ H : HasWeakHessianOn (scaledOpenCubeSet Q rho1) uS,
            H.hessianCoordL2NormSum ≤
              ∑ i : Fin d, ∑ _j : Fin d,
                WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestReducedBound
                  (ρ₁ := rho1) (ρ₂ := rho2) u.toH1Function
                    (oneStepShellForcingH1 M n h omega p Q hh).divergence
                    i theta := by
  obtain ⟨uS, huSfun, huSgrad, H, hH⟩ :=
    exists_oneStepShellNeumann_innerWeakHessian M n h omega p Q hh u hu
      hV eta hetaSub hinnerV theta hVnu hnuNonneg hnuSigma hsigmaOne
      hsigmaTwoNonneg hsigmaTwo hrhoNonneg
  refine ⟨uS, huSfun, huSgrad, H, hH.trans ?_⟩
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun _j _ =>
    WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestBound_le_reducedBound
      u.toH1Function
      (oneStepShellForcingH1 M n h omega p Q hh).divergence i theta

/-- Canonical half-parent specialization of the Neumann interior Hessian.
Every cell contained in this half cube may subsequently restrict the same
witness, so boundary cells are the only ones discarded in the thermodynamic
average. -/
theorem exists_oneStepShellNeumann_innerHalfWeakHessian_reduced
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p : Vec d)
    (Q : TriadicCube d) (hh : 0 < h)
    (u : H1MeanZeroFunction (openCubeSet Q))
    (hu : IsMeanZeroNeumannRhsWeakSolution
      (identityCoeffField d) (openCubeSet Q) u
      (fun x => -(oneStepShellForcingH1 M n h omega p Q hh).toField x)) :
    ∃ uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)),
      uS.toFun = u.toH1Function.toFun ∧
        uS.grad = u.toH1Function.grad ∧
          ∃ H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS,
            H.hessianCoordL2NormSum ≤
              ∑ i : Fin d, ∑ _j : Fin d,
                @WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestReducedBound
                  d Q u.toH1Function
                  (oneStepShellForcingH1 M n h omega p Q hh).divergence i
                  (1 / 2 : ℝ) (7 / 12 : ℝ) (3 / 4 : ℝ) (7 / 8 : ℝ)
                  (CubeCalderonZygmund.outerThreeQuarterSevenEighthCutoff Q) := by
  let V : Set (Vec d) := scaledOpenCubeSet Q (2 / 3 : ℝ)
  have hV : IsOpenBoundedConvexDomain V :=
    isOpenBoundedConvexDomain_scaledOpenCubeSet_of_pos Q (by norm_num)
  have hetaSub :
      tsupport (CubeCalderonZygmund.innerHalfSevenTwelfthCutoff Q : Vec d → ℝ) ⊆ V := by
    have hclosed := QuantitativeCubeCutoff.tsupport_subset_scaledClosedCubeSet_of_support_subset
        (CubeCalderonZygmund.innerHalfSevenTwelfthCutoff Q)
    exact hclosed.trans
      (scaledClosedCubeSet_subset_scaledOpenCubeSet_of_lt Q (by norm_num))
  have hinnerV : scaledClosedCubeSet Q (1 / 2 : ℝ) ⊆ V :=
    scaledClosedCubeSet_subset_scaledOpenCubeSet_of_lt Q (by norm_num)
  have hVnu : V ⊆ scaledClosedCubeSet Q (2 / 3 : ℝ) :=
    scaledOpenCubeSet_subset_scaledClosedCubeSet Q (2 / 3 : ℝ)
  simpa [V] using
    exists_oneStepShellNeumann_innerWeakHessian_reduced M n h omega p Q hh u hu
      hV (CubeCalderonZygmund.innerHalfSevenTwelfthCutoff Q) hetaSub hinnerV
      (CubeCalderonZygmund.outerThreeQuarterSevenEighthCutoff Q) hVnu
      (by norm_num : 0 ≤ (2 / 3 : ℝ)) (by norm_num : (2 / 3 : ℝ) < 3 / 4)
      (by norm_num : (3 / 4 : ℝ) < 1) (by norm_num : 0 ≤ (7 / 8 : ℝ))
      (by norm_num : (7 / 8 : ℝ) < 1) (by norm_num : 0 ≤ (1 / 2 : ℝ))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
