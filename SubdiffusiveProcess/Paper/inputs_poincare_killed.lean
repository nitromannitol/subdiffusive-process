module

public import SubdiffusiveProcess.Paper.inputs_poincare_gradient
public import SubdiffusiveProcess.Paper.inputs_poincare_killed_endpoint
public import SubdiffusiveProcess.Paper.inputs_poincare_killed_transport
public import SubdiffusiveProcess.Frozen.Section2.CoarseGrainedPoincare

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

theorem inputs_poincare_killed (d : ℕ) (hd : 2 ≤ d) (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) :
    (∃ C : ℝ, 0 < C ∧ (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (a : PositiveCoefficient (centeredCube z r hr))
      (u : killedSobolevGraph (centeredCube z r hr)),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ /
          Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) ≤
        C * r * (Jc.lam z r hr a z r 1 1) ^ (-(1 / 2) : ℝ) *
          normalizedEnergyNorm a (centeredCube z r hr).isOpen.measurableSet
            (sobolevGradient (u : SobolevData _)))) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨K, hK, hreadout⟩ := inputs_poincare_killed_endpoint (d := d)
  let P := SubdiffusiveProcess.CoarseGrainingVocab.paperPoincareGeometricFactor 1 (.finite 1)
  have hdiscount : 0 < Homogenization.Book.Ch02.geometricDiscount 1 1 := by
    norm_num [Homogenization.Book.Ch02.geometricDiscount]
  have hP : 0 < P := by
    change 0 < SubdiffusiveProcess.CoarseGrainingVocab.paperPoincareGeometricFactor 1 (.finite 1)
    rw [SubdiffusiveProcess.CoarseGrainingVocab.paperPoincareGeometricFactor]
    exact Real.rpow_pos_of_pos hdiscount _
  refine ⟨K * P, mul_pos hK hP, ?_⟩
  intro z r hr a u
  obtain ⟨v, hL2, hEnergy⟩ := inputs_poincare_killed_transport d hd Jc z r hr a u
  let Q := Homogenization.originCube d 0
  let A := Jc.chart z r hr a z r
  let As := aux_inputs_poincare_gradient_symmFamily A
  have hzero : Homogenization.MemVectorL2 (Homogenization.openCubeSet Q)
      (fun _ : Homogenization.Vec d => 0) := by
    rw [Homogenization.MemVectorL2, Homogenization.volumeMeasureOn]
    exact MeasureTheory.MemLp.zero
  have hsource := SubdiffusiveProcess.Frozen.Section2.coarse_grained_poincare
    hd As (fun R => aux_inputs_poincare_gradient_symmFamily_symmetric A R)
    1 (by norm_num) (by norm_num)
    (Homogenization.Book.Ch02.MultiscaleExponent.finite 1) (by norm_num)
    0 v.toH1Function (fun _ => 0) hzero (Homogenization.isSolenoidalOn_zero)
  have hlam : Jc.lam z r hr a z r 1 1 =
      SubdiffusiveProcess.CoarseGrainingVocab.lambda Q 1 (.finite 1) As := by
    simpa [Q, A, As] using aux_inputs_poincare_gradient_lambda_symm Jc z r hr a
      1 (by norm_num) 1 (by norm_num)
  have hEnergySymm : SubdiffusiveProcess.CoarseGrainingVocab.coefficientEnergyNorm Q As v.toH1Function.grad =
      SubdiffusiveProcess.CoarseGrainingVocab.coefficientEnergyNorm Q A v.toH1Function.grad := by
    unfold SubdiffusiveProcess.CoarseGrainingVocab.coefficientEnergyNorm
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change Homogenization.vecDot (v.toH1Function.grad x)
        (Homogenization.matVecMul
          (Homogenization.symmPart ((A.coeffOn Q).toCoeffField x)) (v.toH1Function.grad x)) = _
      exact Homogenization.vecDot_matVecMul_symmPart _ _
  have hcoarse : SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm Q
      1 (.finite 1) v.toH1Function.grad ≤
      P * (Jc.lam z r hr a z r 1 1) ^ (-(1 / 2) : ℝ) *
        SubdiffusiveProcess.CoarseGrainingVocab.coefficientEnergyNorm Q A v.toH1Function.grad := by
    have hh := hsource.1
    simp only [neg_div] at hh
    change SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm Q
      1 (.finite 1) v.toH1Function.grad ≤
      P * (SubdiffusiveProcess.CoarseGrainingVocab.lambda Q 1 (.finite 1) As) ^ (-(1 / 2) : ℝ) *
        SubdiffusiveProcess.CoarseGrainingVocab.coefficientEnergyNorm Q As v.toH1Function.grad at hh
    rw [← hlam, hEnergySymm] at hh
    exact hh
  have hbound := (hreadout v).trans (mul_le_mul_of_nonneg_left hcoarse hK.le)
  rw [hL2, hEnergy] at hbound
  convert hbound using 1 ; ring

end SubdiffusiveProcess.Paper

