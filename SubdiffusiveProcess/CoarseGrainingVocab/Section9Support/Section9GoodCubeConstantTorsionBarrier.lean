import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeConstantTorsionComparison
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumSmoothSolution
/-! Smooth compactly supported lower barriers for constant-coefficient torsion. -/

set_option autoImplicit false
open Homogenization MeasureTheory Filter SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Compare torsion with an explicitly rescaled smooth cutoff using its Laplacian bound. -/
theorem goodCube_smoothCutoff_le_constantTorsion
    {d : ℕ} [NeZero d] {W : Set (Vec d)} (hW : IsOpenBoundedConvexDomain W)
    {sigma M : ℝ} (hsigma : 0 < sigma) (hM : 0 < M)
    (eta : Vec d → ℝ) (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaC : HasCompactSupport eta) (hetaW : tsupport eta ⊆ W)
    (hDelta : ∀ x ∈ W, -coeffFluxDiv (fun _ => 1) eta x ≤ M)
    (u : H10Function W)
    (hu : IsMassiveWeakSolutionOn (fun _ => sigma) (fun _ => 1) 0 W
      u.toH1Function (fun _ => 1)) :
    ∀ᵐ x ∂volume.restrict W, eta x / (sigma * M) ≤ u.toH1Function.toFun x := by
  letI : IsFiniteMeasure (volume.restrict W) := hW.isFiniteMeasure_restrict_volume
  have hne : sigma * M ≠ 0 := ne_of_gt (mul_pos hsigma hM)
  let e : H10Function W := H10Function.ofContDiff hW.isOpen heta hetaC hetaW
  let v : H10Function W := (sigma * M)⁻¹ • e
  have hvval : v.toH1Function.toFun = fun x => (sigma * M)⁻¹ * eta x := by
    show ((sigma * M)⁻¹ • e.toH1Function).toFun = _
    rw [H1Function.smul_toFun]
    rfl
  have hgradv : v.toH1Function.grad = fun x => (sigma * M)⁻¹ • euclideanGradient eta x := by
    show ((sigma * M)⁻¹ • e.toH1Function).grad = _
    rw [H1Function.smul_grad]
    rfl
  have hv : ∀ phi : H10Function W, (∀ x, 0 ≤ phi.toH1Function.toFun x) →
      sigma * (∫ x in W, vecDot (v.toH1Function.grad x) (phi.toH1Function.grad x) ∂volume) ≤
        ∫ x in W, phi.toH1Function.toFun x ∂volume := by
    intro phi hphi
    have hphiint : Integrable (fun x => phi.toH1Function.toFun x) (volume.restrict W) :=
      phi.toH1Function.memL2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hprodint : Integrable
        (fun x => (-coeffFluxDiv (fun _ => 1) eta x) * phi.toH1Function.toFun x)
        (volume.restrict W) :=
      MemLp.integrable_mul (memScalarL2_neg_coeffFluxDiv contDiff_const heta hetaC W)
        phi.toH1Function.memL2
    have hMint : Integrable (fun x => M * phi.toH1Function.toFun x) (volume.restrict W) :=
      hphiint.const_mul M
    have hflux : coeffFlux (fun _ => 1) eta = euclideanGradient eta := by
      funext x i
      change 1 * euclideanCoordDeriv i eta x = euclideanCoordDeriv i eta x
      exact one_mul _
    have hIBP : ∫ x in W, vecDot (euclideanGradient eta x) (phi.toH1Function.grad x) ∂volume
        = ∫ x in W, (-coeffFluxDiv (fun _ => 1) eta x) * phi.toH1Function.toFun x ∂volume := by
      have h := setIntegral_coeffFlux_dot_h10grad (c := fun _ => 1) contDiff_const heta hetaC
        hW.isOpen phi
      rw [hflux] at h
      exact h
    have hbound : ∫ x in W, (-coeffFluxDiv (fun _ => 1) eta x) * phi.toH1Function.toFun x ∂volume
        ≤ M * ∫ x in W, phi.toH1Function.toFun x ∂volume := by
      have h1 : ∫ x in W, (-coeffFluxDiv (fun _ => 1) eta x) * phi.toH1Function.toFun x ∂volume
          ≤ ∫ x in W, M * phi.toH1Function.toFun x ∂volume :=
        integral_mono_ae hprodint hMint (by
          filter_upwards [ae_restrict_mem hW.isOpen.measurableSet] with x hx
          exact mul_le_mul_of_nonneg_right (hDelta x hx) (hphi x))
      rw [integral_const_mul M (fun x => phi.toH1Function.toFun x)] at h1
      exact h1
    calc sigma * (∫ x in W, vecDot (v.toH1Function.grad x) (phi.toH1Function.grad x) ∂volume)
        = sigma * ((sigma * M)⁻¹ *
            ∫ x in W, vecDot (euclideanGradient eta x) (phi.toH1Function.grad x) ∂volume) := by
          rw [hgradv]
          simp_rw [vecDot_smul_left]
          rw [integral_const_mul]
      _ = sigma * ((sigma * M)⁻¹ *
            ∫ x in W, (-coeffFluxDiv (fun _ => 1) eta x) * phi.toH1Function.toFun x ∂volume) := by
          rw [hIBP]
      _ ≤ sigma * ((sigma * M)⁻¹ * (M * ∫ x in W, phi.toH1Function.toFun x ∂volume)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (mul_pos hsigma hM).le))
            hsigma.le
      _ = ∫ x in W, phi.toH1Function.toFun x ∂volume := by
          have h2 : sigma * ((sigma * M)⁻¹ * (M * ∫ x in W, phi.toH1Function.toFun x ∂volume))
              = (sigma * ((sigma * M)⁻¹ * M)) *
                (∫ x in W, phi.toH1Function.toFun x ∂volume) := by ring
          have h3 : sigma * ((sigma * M)⁻¹ * M) = 1 := by
            have h4 : sigma * ((sigma * M)⁻¹ * M) = (sigma * M) * (sigma * M)⁻¹ := by ring
            rw [h4, mul_inv_cancel₀ hne]
          rw [h2, h3, one_mul]
  have hcmp := goodCube_ae_le_constantTorsion_of_subsolution hW hsigma v u hv hu
  have heq : ∀ x, v.toH1Function.toFun x = eta x / (sigma * M) := fun x => by
    rw [hvval, div_eq_inv_mul]
  refine hcmp.mono (fun x hx => ?_)
  rw [← heq x]
  exact hx

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
