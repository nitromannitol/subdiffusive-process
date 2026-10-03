module

public import SubdiffusiveProcess.Lane4.Inputs
public import SubdiffusiveProcess.Lane2.NativeBridge
public import SubdiffusiveProcess.Lane2.VecDotForm
public import SubdiffusiveProcess.Paper.inputs_classical_e2_gradient

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

def aux_inputs_W_gradient_h10SetEq {d : ℕ} {U V : Set (SpatialCoordinates d)}
    (h : U = V) (phi : H10Function U) : H10Function V := h ▸ phi

@[simp] theorem aux_inputs_W_gradient_h10SetEq_toFun {d : ℕ}
    {U V : Set (SpatialCoordinates d)} (h : U = V) (phi : H10Function U) :
    (aux_inputs_W_gradient_h10SetEq h phi).toH1Function.toFun = phi.toH1Function.toFun := by
  cases h
  rfl

@[simp] theorem aux_inputs_W_gradient_h10SetEq_grad {d : ℕ}
    {U V : Set (SpatialCoordinates d)} (h : U = V) (phi : H10Function U) :
    (aux_inputs_W_gradient_h10SetEq h phi).toH1Function.grad = phi.toH1Function.grad := by
  cases h
  rfl

theorem inputs_W_gradient (d : ℕ) :
    ∀ (p1 : ℝ), 2 ≤ p1 →
      ∃ C epsilon : ℝ, 0 < C ∧ 0 < epsilon ∧ ∀ (x0 : SpatialCoordinates d) (l : ℝ)
      (hl : (0 : ℝ) < 4 * l) (a : PositiveCoefficient (centeredCube x0 (4 * l) hl))
      (a0 : ℝ), 0 < a0 →
      (∀ᵐ y ∂volume.restrict (centeredCube x0 (4 * l) hl : Set (SpatialCoordinates d)),
        |Real.log (a.val y) - Real.log a0| ≤ epsilon) →
      ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
        AEMeasurable F (volume.restrict (centeredCube x0 (4 * l) hl :
            Set (SpatialCoordinates d))) →
        0 ≤ Kf →
        (∀ᵐ y ∂volume.restrict (centeredCube x0 (4 * l) hl : Set (SpatialCoordinates d)),
          |F y| ≤ Kf) →
      ∀ u : weakSobolevGraph (centeredCube x0 (4 * l) hl),
        (∀ φ : killedSobolevGraph (centeredCube x0 (4 * l) hl),
          sobolevCoefficientForm a (u : SobolevData (centeredCube x0 (4 * l) hl))
              (φ : SobolevData (centeredCube x0 (4 * l) hl)) =
            ∫ y in (centeredCube x0 (4 * l) hl : Set (SpatialCoordinates d)),
              F y * (φ : SobolevData (centeredCube x0 (4 * l) hl)).1 y) →
        MemLp (fun y => Real.sqrt (∑ i : Fin d,
              ((sobolevGradient (u : SobolevData (centeredCube x0 (4 * l) hl))) i y) ^ 2))
            (ENNReal.ofReal p1)
            ((volume.restrict (centeredCube x0 (4 * l) hl : Set (SpatialCoordinates d))).restrict
              (Metric.ball x0 l)) ∧
          normalizedGradientLpNorm (ENNReal.ofReal p1) (Metric.ball x0 l)
              (sobolevGradient (u : SobolevData (centeredCube x0 (4 * l) hl))) ≤
            C * normalizedGradientLpNorm 2 (Metric.ball x0 (2 * l))
                (sobolevGradient (u : SobolevData (centeredCube x0 (4 * l) hl))) +
              C * l * a0⁻¹ * Kf := by
  intro p1 hp1
  obtain ⟨epsClass, C, hepsClass, hepsClass_le, hC, hclass⟩ :=
    Paper.inputs_classical_e2_gradient d p1 hp1
  let epsLog : ℝ := Real.log (1 + epsClass)
  have hepsLog : 0 < epsLog := by
    dsimp [epsLog]
    apply Real.log_pos
    linarith
  have hexp : Real.exp epsLog - 1 = epsClass := by
    dsimp [epsLog]
    rw [Real.exp_log]
    · ring
    · linarith
  refine ⟨C, epsLog, hC, hepsLog, ?_⟩
  intro x0 l hl a a0 ha0 hlog F Kf hF hKf hFbound u heq
  have hlpos : 0 < l := by nlinarith
  let Ω := centeredCube x0 (4 * l) hl
  have hset : (Ω : Set (SpatialCoordinates d)) = Metric.ball x0 (2 * l) := by
    dsimp [Ω, centeredCube]
    congr 1
    ring
  have hμ : volume.restrict (Ω : Set (SpatialCoordinates d)) =
      volume.restrict (Metric.ball x0 (2 * l)) := by rw [hset]
  have hμCube : volume.restrict
      (centeredCube x0 (4 * l) hl : Set (SpatialCoordinates d)) =
      volume.restrict (Metric.ball x0 (2 * l)) := hμ
  have hsmall : Metric.ball x0 l ⊆ Metric.ball x0 (2 * l) :=
    Metric.ball_subset_ball (by linarith)
  have hμsmall :
      (volume.restrict (centeredCube x0 (4 * l) hl : Set (SpatialCoordinates d))).restrict
          (Metric.ball x0 l) = volume.restrict (Metric.ball x0 l) := by
    rw [hμCube, Measure.restrict_restrict_of_subset hsmall]
  have hsetIntegral (f : SpatialCoordinates d → ℝ) :
      (∫ y in (Ω : Set (SpatialCoordinates d)), f y) =
        ∫ y in Metric.ball x0 (2 * l), f y := by
    exact congrArg (fun s : Set (SpatialCoordinates d) => ∫ y in s, f y) hset
  obtain ⟨c, hc, hcae⟩ := a.property
  have haposΩ : ∀ᵐ y ∂volume.restrict (Ω : Set (SpatialCoordinates d)), 0 < a.val y := by
    filter_upwards [hcae] with y hy
    exact lt_of_lt_of_le hc hy
  have hapos : ∀ᵐ y ∂volume.restrict (Metric.ball x0 (2 * l)), 0 < a.val y := by
    simpa only [← hμ] using haposΩ
  have hlogBall : ∀ᵐ y ∂volume.restrict (Metric.ball x0 (2 * l)),
      |Real.log (a.val y) - Real.log a0| ≤ epsLog := by
    simpa only [← hμ, epsLog] using hlog
  have hosc : ∀ᵐ y ∂volume.restrict (Metric.ball x0 (2 * l)),
      |a.val y - a0| ≤ epsClass * a0 := by
    filter_upwards [hapos, hlogBall] with y hypos hylog
    have hratio :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.abs_div_sub_one_le_exp_of_log_oscillation
        hypos ha0 hylog
    rw [hexp] at hratio
    have hmul : a0 * (a.val y / a0 - 1) = a.val y - a0 := by
      field_simp [ne_of_gt ha0]
    rw [← hmul, abs_mul, abs_of_pos ha0]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hratio ha0.le
  have hAEMeasurableA : AEMeasurable (fun y : Vec d => a.val y)
      (volume.restrict (Metric.ball x0 (2 * l))) := by
    have hAEMeasurableAΩ : AEMeasurable (fun y : Vec d => a.val y)
        (volume.restrict (Ω : Set (SpatialCoordinates d))) :=
      (Lp.aestronglyMeasurable a.val).aemeasurable
    exact hμ ▸ hAEMeasurableAΩ
  have hFball : AEMeasurable F (volume.restrict (Metric.ball x0 (2 * l))) := by
    change AEMeasurable F (volume.restrict (Ω : Set (SpatialCoordinates d))) at hF
    exact hμ ▸ hF
  have hFboundBall : ∀ᵐ y ∂volume.restrict (Metric.ball x0 (2 * l)), |F y| ≤ Kf := by
    change ∀ᵐ y ∂volume.restrict (Ω : Set (SpatialCoordinates d)), |F y| ≤ Kf at hFbound
    exact hμ ▸ hFbound
  obtain ⟨v, hvval, hvgrad⟩ :=
    SubdiffusiveProcess.exists_nativeH1Function_of_weakSobolevGraph u
  let uClass : H1Function (Metric.ball x0 (2 * l)) :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.h1FunctionOfSetEq hset v
  have hvdata : SubdiffusiveProcess.sobolevDataOfH1 v =
      (u : SobolevData Ω) := by
    apply Prod.ext
    · apply Lp.ext
      filter_upwards [SubdiffusiveProcess.sobolevDataOfH1_fst_coeFn v] with y hy
      rw [hy, hvval]
    · funext i
      apply Lp.ext
      filter_upwards [SubdiffusiveProcess.sobolevDataOfH1_snd_coeFn v i] with y hy
      rw [hy, hvgrad]
  have hclassWeak : ∀ phi : H10Function (Metric.ball x0 (2 * l)),
      (∫ x in Metric.ball x0 (2 * l),
        a.val x * (∑ i : Fin d, uClass.grad x i * phi.toH1Function.grad x i)) =
      ∫ x in Metric.ball x0 (2 * l), F x * phi.toH1Function.toFun x := by
    intro phi
    let phiΩ : H10Function (Ω : Set (SpatialCoordinates d)) :=
      aux_inputs_W_gradient_h10SetEq hset.symm phi
    have hphiVal : phiΩ.toH1Function.toFun = phi.toH1Function.toFun := by simp [phiΩ]
    have hphiGrad : phiΩ.toH1Function.grad = phi.toH1Function.grad := by simp [phiΩ]
    have hphiKilled :
        SubdiffusiveProcess.sobolevDataOfH1 phiΩ.toH1Function ∈
          killedSobolevGraph Ω :=
      SubdiffusiveProcess.sobolevDataOfH1_mem_killed phiΩ
    let phiGraph : killedSobolevGraph Ω := ⟨
      SubdiffusiveProcess.sobolevDataOfH1 phiΩ.toH1Function, hphiKilled⟩
    have heqφ := heq phiGraph
    change sobolevCoefficientForm a (u : SobolevData Ω)
        (SubdiffusiveProcess.sobolevDataOfH1 phiΩ.toH1Function) =
      ∫ y in (Ω : Set (SpatialCoordinates d)), F y *
        (SubdiffusiveProcess.sobolevDataOfH1 phiΩ.toH1Function).1 y at heqφ
    rw [← hvdata] at heqφ
    have hint : ∀ i : Fin d, IntegrableOn
        (fun y => a.val y * (v.grad y i * phiΩ.toH1Function.grad y i))
        (Ω : Set (SpatialCoordinates d)) volume := by
      intro i
      have hroot := SubdiffusiveProcess.integrable_weighted_coordinates a.val
        (sobolevGradient (SubdiffusiveProcess.sobolevDataOfH1 v))
        (sobolevGradient (SubdiffusiveProcess.sobolevDataOfH1 phiΩ.toH1Function)) i
      have hvrep := SubdiffusiveProcess.sobolevDataOfH1_snd_coeFn v i
      have hphirep := SubdiffusiveProcess.sobolevDataOfH1_snd_coeFn phiΩ.toH1Function i
      have hcongr : (fun y => a.val y *
          ((SubdiffusiveProcess.sobolevDataOfH1 v).2 i y *
            (SubdiffusiveProcess.sobolevDataOfH1 phiΩ.toH1Function).2 i y)) =ᵐ[
              volume.restrict (Ω : Set (SpatialCoordinates d))]
          (fun y => a.val y * (v.grad y i * phiΩ.toH1Function.grad y i)) := by
        filter_upwards [hvrep, hphirep] with y hy hpy
        rw [hy, hpy]
      simpa only [IntegrableOn] using hroot.congr hcongr
    have hvec := SubdiffusiveProcess.sobolevCoefficientForm_eq_integral_vecDot
      a v phiΩ.toH1Function hint
    rw [hvec] at heqφ
    have hsource :
        (∫ y in (Ω : Set (SpatialCoordinates d)), F y *
          (SubdiffusiveProcess.sobolevDataOfH1 phiΩ.toH1Function).1 y) =
        ∫ x in Metric.ball x0 (2 * l), F x * phi.toH1Function.toFun x := by
      change (∫ y, F y *
        (SubdiffusiveProcess.sobolevDataOfH1 phiΩ.toH1Function).1 y
          ∂volume.restrict (Ω : Set (SpatialCoordinates d))) =
        (∫ x, F x * phi.toH1Function.toFun x
          ∂volume.restrict (Metric.ball x0 (2 * l)))
      calc
        _ = ∫ y in (Ω : Set (SpatialCoordinates d)), F y * phi.toH1Function.toFun y := by
          apply integral_congr_ae
          filter_upwards [SubdiffusiveProcess.sobolevDataOfH1_fst_coeFn
            phiΩ.toH1Function] with y hy
          rw [hy, hphiVal]
        _ = ∫ x in Metric.ball x0 (2 * l), F x * phi.toH1Function.toFun x :=
          hsetIntegral _
    have hleft :
        (∫ x in Metric.ball x0 (2 * l),
          a.val x * (∑ i : Fin d, uClass.grad x i * phi.toH1Function.grad x i)) =
        ∫ x in Metric.ball x0 (2 * l),
          Homogenization.vecDot (a.val x • v.grad x) (phiΩ.toH1Function.grad x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      have hu : uClass.grad x = v.grad x := by
        exact congrFun
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.h1FunctionOfSetEq_grad hset v) x
      rw [hu, ← hphiGrad]
      calc
        a.val x * (∑ i : Fin d, v.grad x i * phiΩ.toH1Function.grad x i) =
            ∑ i : Fin d, a.val x *
              (v.grad x i * phiΩ.toH1Function.grad x i) := by
                rw [Finset.mul_sum]
        _ = ∑ i : Fin d,
            (a.val x * v.grad x i) * phiΩ.toH1Function.grad x i := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = Homogenization.vecDot (a.val x • v.grad x)
            (phiΩ.toH1Function.grad x) := by
              simp [Homogenization.vecDot, Pi.smul_apply, smul_eq_mul]
    have heqφΩ :
        (∫ x in (Ω : Set (SpatialCoordinates d)),
          Homogenization.vecDot (a.val x • v.grad x)
            (phiΩ.toH1Function.grad x)) =
        ∫ y in (Ω : Set (SpatialCoordinates d)), F y *
          (SubdiffusiveProcess.sobolevDataOfH1 phiΩ.toH1Function).1 y := by
      change _ = _ at heqφ
      exact heqφ
    exact hleft.trans ((hsetIntegral _).symm.trans (heqφΩ.trans hsource))
  have hresult := hclass x0 l hlpos (fun y => a.val y) a0 ha0 hAEMeasurableA hosc
    F Kf hFball hKf hFboundBall uClass hclassWeak
  refine ⟨?_, ?_⟩
  · have hgradFun :
        (fun y => Real.sqrt (∑ i : Fin d,
          ((sobolevGradient (u : SobolevData Ω)) i y) ^ 2)) =
        (fun y => Real.sqrt (∑ i : Fin d, (uClass.grad y i) ^ 2)) := by
      funext y
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      simp [sobolevGradient, uClass,
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.h1FunctionOfSetEq_grad, hvgrad]
    change MemLp
      (fun y => Real.sqrt (∑ i : Fin d,
        ((sobolevGradient (u : SobolevData Ω)) i y) ^ 2))
      (ENNReal.ofReal p1)
      ((volume.restrict (centeredCube x0 (4 * l) hl : Set (SpatialCoordinates d))).restrict
        (Metric.ball x0 l))
    rw [hgradFun, hμsmall]
    exact hresult.1
  · have hnormSmall := hresult.2
    have hnormId :
        normalizedGradientLpNorm (ENNReal.ofReal p1) (Metric.ball x0 l)
            (sobolevGradient (u : SobolevData Ω)) =
          (eLpNorm (fun x => Real.sqrt (∑ i : Fin d, (uClass.grad x i) ^ 2))
            (ENNReal.ofReal p1) (volume.restrict (Metric.ball x0 l))).toReal /
            (volume.real (Metric.ball x0 l)) ^ (1 / p1) := by
      simp [normalizedGradientLpNorm, hμsmall, uClass,
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.h1FunctionOfSetEq_grad, hvgrad,
        sobolevGradient, ENNReal.toReal_ofReal (le_trans (by norm_num) hp1)]
    have hnormBig :
        normalizedGradientLpNorm 2 (Metric.ball x0 (2 * l))
            (sobolevGradient (u : SobolevData Ω)) =
          (eLpNorm (fun x => Real.sqrt (∑ i : Fin d, (uClass.grad x i) ^ 2))
            2 (volume.restrict (Metric.ball x0 (2 * l)))).toReal /
            (volume.real (Metric.ball x0 (2 * l))) ^ (1 / 2 : ℝ) := by
      have hμbig :
          (volume.restrict (centeredCube x0 (4 * l) hl : Set (SpatialCoordinates d))).restrict
              (Metric.ball x0 (2 * l)) = volume.restrict (Metric.ball x0 (2 * l)) := by
        rw [hμCube, Measure.restrict_restrict_of_subset
          (show Metric.ball x0 (2 * l) ⊆ Metric.ball x0 (2 * l) from Subset.rfl)]
      simp [normalizedGradientLpNorm, hμbig, uClass,
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.h1FunctionOfSetEq_grad, hvgrad,
        sobolevGradient]
    rw [← hnormId, ← hnormBig] at hnormSmall
    exact hnormSmall

end Paper

