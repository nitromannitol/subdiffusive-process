module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.MassiveMaximumPrinciple
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.MaxPrinciple
@[expose] public section

/-! The zero-mass maximum principle from truncation and zero-trace Poincare. -/

set_option autoImplicit false
open Homogenization MeasureTheory Filter SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- A zero-trace weak subsolution with nonpositive Laplacian pairing is nonpositive. -/
theorem goodCube_ae_nonpos_of_nonpos_laplacian_pairing
    {d : ℕ} [NeZero d] {W : Set (Vec d)} (hW : IsOpenBoundedConvexDomain W)
    (v : H10Function W)
    (hv : ∀ phi : H10Function W, (∀ x, 0 ≤ phi.toH1Function.toFun x) →
      (∫ x in W, vecDot (v.toH1Function.grad x) (phi.toH1Function.grad x) ∂volume) ≤ 0) :
    ∀ᵐ x ∂volume.restrict W, v.toH1Function.toFun x ≤ 0 := by
  obtain ⟨w, hwval, hwgrad⟩ := exists_h10_positivePart hW v (le_refl 0)
  have hae : (fun y => vecDot (v.toH1Function.grad y) (w.toH1Function.grad y)) =ᵐ[volume.restrict W]
      (fun y => vecNormSq (w.toH1Function.grad y)) := by
    filter_upwards [hwgrad] with y hy
    by_cases hmem : y ∈ {p | 0 < v.toH1Function.toFun p}
    · rw [hy, Set.indicator_of_mem hmem, vecNormSq]
    · rw [hy, Set.indicator_of_notMem hmem]
      simp [vecDot, vecNormSq]
  have hint : Integrable (fun y => vecNormSq (w.toH1Function.grad y)) (volume.restrict W) := by
    simpa [IntegrableOn, volumeMeasureOn, vecNormSq] using
      SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.integrableOn_vecDot_grad
        w.toH1Function w.toH1Function
  have hnn : ∀ᵐ y ∂(volume.restrict W), 0 ≤ vecNormSq (w.toH1Function.grad y) :=
    Filter.Eventually.of_forall fun y => Homogenization.vecNormSq_nonneg _
  have hpair : (∫ y in W, vecDot (v.toH1Function.grad y) (w.toH1Function.grad y) ∂volume) = 0 := by
    have hle := hv w (fun x => by rw [hwval x]; exact le_max_right _ _)
    have hge : 0 ≤ ∫ y in W, vecDot (v.toH1Function.grad y) (w.toH1Function.grad y) ∂volume := by
      rw [integral_congr_ae hae]
      exact integral_nonneg_of_ae hnn
    exact le_antisymm hle hge
  have hnorm : (∫ y in W, vecNormSq (w.toH1Function.grad y) ∂volume) = 0 := by
    rw [← integral_congr_ae hae]
    exact hpair
  have hgz : (fun y => vecNormSq (w.toH1Function.grad y)) =ᵐ[volume.restrict W] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 hnorm
  have hgradzero : w.toH1Function.grad =ᵐ[volume.restrict W] 0 := by
    filter_upwards [hgz] with y hy
    refine Homogenization.vecNormSq_eq_zero ?_
    simpa using hy
  have hVL2 : w.toH1Function.gradToVectorL2 = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [w.toH1Function.coeFn_gradToVectorL2, hgradzero] with y h1 h2
    rw [h1, h2]
  have hS :=
    Homogenization.H10Function.toScalarL2_eq_zero_of_gradToVectorL2_eq_zero_of_exists_poincare_constant
      (Homogenization.H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain hW)
      w hVL2
  have hval : w.toH1Function.toFun =ᵐ[volume.restrict W] 0 := by
    have hc := w.toH1Function.coeFn_toScalarL2
    rw [hS] at hc
    filter_upwards [hc, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := volume.restrict W)] with y h1 h2
    rw [← h1, h2]
  filter_upwards [hval] with y hy
  have hmax : max (v.toH1Function.toFun y - 0) 0 = 0 := by
    rw [← hwval y]
    exact hy
  have hle := max_eq_right_iff.1 hmax
  linarith only [hle]

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
