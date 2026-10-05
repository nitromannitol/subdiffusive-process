module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepHarmonicHighExponent
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepWeakHessianDilation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepAxisCubeHarmonicHessian
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.AxisCubeHarmonicCovariance

@[expose] public section

/-!
# Arbitrary-axis harmonic Hessian existence

The fixed-cube interior Hessian package is transported through the exact
positive affine parametrization of an arbitrary axis cube.  This supplies the
existence half of the translated Neumann cell estimate; the Hessian
scales by the inverse side length.
-/

open MeasureTheory Homogenization
open scoped ENNReal Pointwise

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private theorem centralDescendant_centralChild_eq {d : ℕ}
    (Q : TriadicCube d) (n : ℕ) :
    CubeCalderonZygmund.centralDescendant
        (CubeCalderonZygmund.centralChild Q) n =
      CubeCalderonZygmund.centralDescendant Q (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [CubeCalderonZygmund.centralDescendant_succ, ih]
      rfl

/-- The affine image of the fixed centered half cube inside `axisCube z L`. -/
def axisCubeInnerHalf {d : ℕ} (z : Vec d) (L : ℝ) : Set (Vec d) :=
  translateSet (CubeCalderonZygmund.axisCubeCenter z L)
    (L • scaledOpenCubeSet (originCube d 0) (1 / 2 : ℝ))

/-- The fixed-cube harmonic Hessian witness, pushed onto an arbitrary
positive axis cube.  Besides retaining the original function and gradient,
the theorem records the literal inverse-length Hessian formula needed for
normalized cell estimates. -/
theorem exists_axisCube_harmonic_innerHalf_weakHessian
    (d : ℕ) (hd : 3 ≤ d) :
    ∃ depth : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (z : Vec d) (L : ℝ) (hL : 0 < L),
        ∀ (u : H1Function (axisCube z L)),
          WeakPoissonEquationOn (axisCube z L) u (fun _ ↦ 0) →
            ∃ vS : H1Function
                (scaledOpenCubeSet (originCube d 0) (1 / 2 : ℝ)),
              vS.toFun =
                  (CubeCalderonZygmund.axisCubeHarmonicPullback z hL u).toFun ∧
              vS.grad =
                  (CubeCalderonZygmund.axisCubeHarmonicPullback z hL u).grad ∧
              ∃ uS : H1Function (axisCubeInnerHalf z L),
                uS.toFun = u.toFun ∧ uS.grad = u.grad ∧
                  ∃ H : HasWeakHessianOn (axisCubeInnerHalf z L) uS,
                    ∃ H0 : HasWeakHessianOn
                      (scaledOpenCubeSet (originCube d 0) (1 / 2 : ℝ)) vS,
                      (∀ i j : Fin d,
                        MemLp (fun x ↦ H0.hess i j x)
                            (oneStepHarmonicExponent d hd).exponent
                            (normalizedCubeMeasure
                              (CubeCalderonZygmund.centralDescendant
                                (CubeCalderonZygmund.centralChild
                                  (originCube d 0)) depth)) ∧
                          cubeLpNorm
                              (CubeCalderonZygmund.centralDescendant
                                (CubeCalderonZygmund.centralChild
                                  (originCube d 0)) depth)
                              (oneStepHarmonicExponent d hd).exponent
                              (fun x ↦ H0.hess i j x) ≤
                            C * (cubeScaleFactor (originCube d 0))⁻¹ *
                              ∑ k : Fin d,
                                cubeLpNorm (originCube d 0) 2
                                  (fun x ↦
                                    (CubeCalderonZygmund.axisCubeHarmonicPullback
                                      z hL u).grad x k)) ∧
                      ∀ i j x, H.hess i j x =
                        L⁻¹ * H0.hess i j
                          (L⁻¹ •
                            (x - CubeCalderonZygmund.axisCubeCenter z L)) := by
  obtain ⟨depth, C, hC, hfixed⟩ :=
    exists_harmonic_fixedInterior_hessian_highExponent_bound d hd
  refine ⟨depth, C, hC, ?_⟩
  intro z L hL u hu
  let v := CubeCalderonZygmund.axisCubeHarmonicPullback z hL u
  have hv : WeakPoissonEquationOn (openCubeSet (originCube d 0)) v 0 :=
    CubeCalderonZygmund.axisCubeHarmonicPullback_weakPoisson_zero z hL hu
  obtain ⟨vS, hvSfun, hvSgrad, H0, _hH0⟩ :=
    hfixed (originCube d 0) v hv
  let c := CubeCalderonZygmund.axisCubeCenter z L
  let uS0 : H1Function (axisCubeInnerHalf z L) :=
    (vS.dilateSet hL rfl).translate c
  let H : HasWeakHessianOn (axisCubeInnerHalf z L) uS0 :=
    H0.dilateTranslate hL c
  have huSfun : uS0.toFun = u.toFun := by
    funext x
    change L * vS.toFun (L⁻¹ • (x - c)) = u.toFun x
    rw [congrFun hvSfun (L⁻¹ • (x - c))]
    simp only [v, CubeCalderonZygmund.axisCubeHarmonicPullback_toFun]
    have haffine : CubeCalderonZygmund.axisCubeAffine z L
        (L⁻¹ • (x - c)) = x := by
      unfold CubeCalderonZygmund.axisCubeAffine
      rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
      exact sub_add_cancel x c
    rw [haffine]
    field_simp [hL.ne']
  have huSgrad : uS0.grad = u.grad := by
    funext x
    change vS.grad (L⁻¹ • (x - c)) = u.grad x
    rw [congrFun hvSgrad (L⁻¹ • (x - c))]
    simp only [v, CubeCalderonZygmund.axisCubeHarmonicPullback_grad]
    have haffine : CubeCalderonZygmund.axisCubeAffine z L
        (L⁻¹ • (x - c)) = x := by
      unfold CubeCalderonZygmund.axisCubeAffine
      rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
      exact sub_add_cancel x c
    rw [haffine]
  refine ⟨vS, hvSfun, hvSgrad, uS0, huSfun, huSgrad, H, H0, ?_, ?_⟩
  · simpa only [v] using _hH0
  intro i j x
  rfl

/-- The transported witness satisfies the full normalized high-exponent
estimate on the corresponding concentric target cube.  The right side is the
parent axis-cube gradient norm, and the only dimensional scaling is `L⁻¹`. -/
theorem exists_axisCube_harmonic_innerHalf_hessian_highExponent_bound
    (d : ℕ) (hd : 3 ≤ d) :
    ∃ depth : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (z : Vec d) (L : ℝ), 0 < L →
        ∀ (u : H1Function (axisCube z L)),
          WeakPoissonEquationOn (axisCube z L) u (fun _ ↦ 0) →
          ∃ uS : H1Function (axisCubeInnerHalf z L),
            uS.toFun = u.toFun ∧ uS.grad = u.grad ∧
              ∃ H : HasWeakHessianOn (axisCubeInnerHalf z L) uS,
                ∀ i j : Fin d,
                  MemLp (fun x ↦ H.hess i j x)
                      (oneStepHarmonicExponent d hd).exponent
                      (CubeCalderonZygmund.axisCubeNormalizedMeasure
                        (CubeCalderonZygmund.axisCubeConcentricDepthCorner
                          z L (depth + 1))
                        (CubeCalderonZygmund.axisCubeConcentricDepthSide
                          L (depth + 1))) ∧
                    (eLpNorm (fun x ↦ H.hess i j x)
                        (oneStepHarmonicExponent d hd).exponent
                        (CubeCalderonZygmund.axisCubeNormalizedMeasure
                          (CubeCalderonZygmund.axisCubeConcentricDepthCorner
                            z L (depth + 1))
                          (CubeCalderonZygmund.axisCubeConcentricDepthSide
                            L (depth + 1)))).toReal ≤
                      C * L⁻¹ *
                        ∑ k : Fin d,
                          (eLpNorm (fun x ↦ u.grad x k) 2
                            (CubeCalderonZygmund.axisCubeNormalizedMeasure
                              z L)).toReal := by
  obtain ⟨depth, C, hC, htransport⟩ :=
    exists_axisCube_harmonic_innerHalf_weakHessian d hd
  refine ⟨depth, C, hC, ?_⟩
  intro z L hL u hu
  obtain ⟨vS, hvSfun, hvSgrad, uS, huSfun, huSgrad, H, H0,
      hH0, hformula⟩ := htransport z L hL u hu
  refine ⟨uS, huSfun, huSgrad, H, ?_⟩
  have hsourceCube :
      CubeCalderonZygmund.centralDescendant
          (CubeCalderonZygmund.centralChild (originCube d 0)) depth =
        originCube d (-((depth + 1 : ℕ) : ℤ)) := by
    rw [centralDescendant_centralChild_eq]
    exact CubeCalderonZygmund.centralDescendant_originCube_zero_eq_originCube_neg_nat _
  intro i j
  have hsourceMem : MemLp (fun x ↦ H0.hess i j x)
      (oneStepHarmonicExponent d hd).exponent
      (normalizedCubeMeasure (originCube d (-((depth + 1 : ℕ) : ℤ)))) := by
    simpa only [hsourceCube] using (hH0 i j).1
  have hcomp : (fun x ↦ H.hess i j
      (CubeCalderonZygmund.axisCubeAffine z L x)) =
      fun x ↦ L⁻¹ * H0.hess i j x := by
    funext x
    rw [hformula]
    simp only [CubeCalderonZygmund.axisCubeAffine]
    rw [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hL.ne', one_smul]
  have hcompMem : MemLp
      (fun x ↦ H.hess i j
        (CubeCalderonZygmund.axisCubeAffine z L x))
      (oneStepHarmonicExponent d hd).exponent
      (normalizedCubeMeasure (originCube d (-((depth + 1 : ℕ) : ℤ)))) := by
    rw [hcomp]
    exact hsourceMem.const_mul L⁻¹
  have htargetMem :=
    (CubeCalderonZygmund.memLp_axisCubeAffine_originCube_neg_nat_iff
      z hL.ne' (depth + 1) (oneStepHarmonicExponent d hd).exponent
      (fun x ↦ H.hess i j x)).1 hcompMem
  refine ⟨htargetMem, ?_⟩
  have hnormTransport :=
    CubeCalderonZygmund.eLpNorm_axisCubeAffine_originCube_neg_nat_of_memLp
      z hL.ne' (depth + 1) (oneStepHarmonicExponent d hd).exponent
      (fun x ↦ H.hess i j x) hcompMem
  have hscaledNorm :
      eLpNorm
          (fun x ↦ H.hess i j
            (CubeCalderonZygmund.axisCubeAffine z L x))
          (oneStepHarmonicExponent d hd).exponent
          (normalizedCubeMeasure
            (originCube d (-((depth + 1 : ℕ) : ℤ)))) =
        ENNReal.ofReal L⁻¹ *
          eLpNorm (fun x ↦ H0.hess i j x)
            (oneStepHarmonicExponent d hd).exponent
            (normalizedCubeMeasure
              (originCube d (-((depth + 1 : ℕ) : ℤ)))) := by
    rw [hcomp]
    change eLpNorm (L⁻¹ • (fun x ↦ H0.hess i j x))
      (oneStepHarmonicExponent d hd).exponent
      (normalizedCubeMeasure
        (originCube d (-((depth + 1 : ℕ) : ℤ)))) = _
    rw [MeasureTheory.eLpNorm_const_smul]
    simp [Real.enorm_eq_ofReal_abs, abs_of_pos (inv_pos.mpr hL)]
  have htargetNorm :
      (eLpNorm (fun x ↦ H.hess i j x)
          (oneStepHarmonicExponent d hd).exponent
          (CubeCalderonZygmund.axisCubeNormalizedMeasure
            (CubeCalderonZygmund.axisCubeConcentricDepthCorner
              z L (depth + 1))
            (CubeCalderonZygmund.axisCubeConcentricDepthSide
              L (depth + 1)))).toReal =
        L⁻¹ * cubeLpNorm
          (originCube d (-((depth + 1 : ℕ) : ℤ)))
          (oneStepHarmonicExponent d hd).exponent
          (fun x ↦ H0.hess i j x) := by
    rw [← hnormTransport, hscaledNorm, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr hL.le)]
    rfl
  rw [htargetNorm]
  have hsourceBound : cubeLpNorm
      (originCube d (-((depth + 1 : ℕ) : ℤ)))
      (oneStepHarmonicExponent d hd).exponent
      (fun x ↦ H0.hess i j x) ≤
        C * ∑ k : Fin d,
          cubeLpNorm (originCube d 0) 2
            (fun x ↦
              (CubeCalderonZygmund.axisCubeHarmonicPullback z hL u).grad x k) := by
    have hb := (hH0 i j).2
    rw [hsourceCube] at hb
    simpa [cubeScaleFactor, originCube] using hb
  have hparent : ∀ k : Fin d,
      cubeLpNorm (originCube d 0) 2
          (fun x ↦
            (CubeCalderonZygmund.axisCubeHarmonicPullback z hL u).grad x k) =
        (eLpNorm (fun x ↦ u.grad x k) 2
          (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)).toReal := by
    intro k
    have hmem :=
      (CubeCalderonZygmund.axisCubeHarmonicPullback z hL u).grad_memL2_normalizedCubeMeasure k
    have heq :=
      CubeCalderonZygmund.eLpNorm_axisCubeHarmonicPullback_grad_originCube_neg_nat
        z hL u 0 2 k hmem
    simpa [cubeLpNorm] using congrArg ENNReal.toReal heq
  have hsourceBound' : cubeLpNorm
      (originCube d (-((depth + 1 : ℕ) : ℤ)))
      (oneStepHarmonicExponent d hd).exponent
      (fun x ↦ H0.hess i j x) ≤
        C * ∑ k : Fin d,
          (eLpNorm (fun x ↦ u.grad x k) 2
            (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)).toReal := by
    simpa only [hparent] using hsourceBound
  simpa [mul_assoc, mul_left_comm] using
    (mul_le_mul_of_nonneg_left hsourceBound' (inv_nonneg.mpr hL.le))

/-- Restrict an arbitrary-axis high-exponent Hessian package to a literal
contained triadic cell.  This is the deterministic `B_z` endpoint: the only
localization loss is the exact normalized-volume ratio to the power
`1/(16d)`. -/
theorem oneStepCellB_le_of_axisCube_highExponent
    {d : ℕ} (hd : 3 ≤ d) {V : Set (Vec d)}
    (u : H1Function V) (H : HasWeakHessianOn V u)
    (R : TriadicCube d) (hRV : openCubeSet R ⊆ V)
    (zInner : Vec d) (LInner : ℝ) (hLInner : 0 < LInner)
    (hRinner : openCubeSet R ⊆ axisCube zInner LInner)
    (B : ℝ)
    (hhigh : ∀ i j : Fin d,
      MemLp (fun x ↦ H.hess i j x)
          (oneStepHarmonicExponent d hd).exponent
          (CubeCalderonZygmund.axisCubeNormalizedMeasure zInner LInner) ∧
        (eLpNorm (fun x ↦ H.hess i j x)
          (oneStepHarmonicExponent d hd).exponent
          (CubeCalderonZygmund.axisCubeNormalizedMeasure zInner LInner)).toReal
            ≤ B) :
    oneStepCellB R (H.restrict (isOpen_openCubeSet R) hRV) ≤
      cubeScaleFactor R * (d : ℝ) ^ 2 *
        ((triadicAxisNormalizedMeasureRatio R LInner) ^
          (1 / (oneStepHarmonicExponent d hd).exponent).toReal).toReal * B := by
  let : IsProbabilityMeasure (normalizedCubeMeasure R) :=
    ⟨normalizedCubeMeasure_apply_univ R⟩
  let HR := H.restrict (isOpen_openCubeSet R) hRV
  let ratio : ℝ≥0∞ :=
    (triadicAxisNormalizedMeasureRatio R LInner) ^
      (1 / (oneStepHarmonicExponent d hd).exponent).toReal
  have hratioTop : ratio ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg
    · positivity
    unfold triadicAxisNormalizedMeasureRatio
    exact ENNReal.div_ne_top ENNReal.ofReal_ne_top
      (ENNReal.ofReal_ne_zero_iff.2
        (inv_pos.mpr (pow_pos hLInner d)))
  have hq : ∀ i j : Fin d,
      MemLp (fun x ↦ HR.hess i j x)
          (oneStepHarmonicExponent d hd).exponent
          (normalizedCubeMeasure R) ∧
        cubeLpNorm R (oneStepHarmonicExponent d hd).exponent
            (fun x ↦ HR.hess i j x) ≤ ratio.toReal * B := by
    intro i j
    have hr := eLpNorm_triadic_le_ratio_rpow_mul_axisCube
      R zInner LInner hLInner hRinner (oneStepHarmonicExponent d hd)
      (fun x ↦ H.hess i j x) (hhigh i j).1
    have hmem : MemLp (fun x ↦ HR.hess i j x)
        (oneStepHarmonicExponent d hd).exponent
        (normalizedCubeMeasure R) := by
      simpa only [HR, HasWeakHessianOn.restrict] using hr.1
    refine ⟨hmem, ?_⟩
    have haxisTop := (hhigh i j).1.eLpNorm_ne_top
    have hprodTop : ratio * eLpNorm (fun x ↦ H.hess i j x)
        (oneStepHarmonicExponent d hd).exponent
        (CubeCalderonZygmund.axisCubeNormalizedMeasure zInner LInner) ≠ ∞ :=
      ENNReal.mul_ne_top hratioTop haxisTop
    have hreal := ENNReal.toReal_mono hprodTop hr.2
    rw [ENNReal.toReal_mul] at hreal
    exact hreal.trans (mul_le_mul_of_nonneg_left (hhigh i j).2
      ENNReal.toReal_nonneg)
  have hfour : ∀ i j : Fin d,
      MemLp (fun x ↦ HR.hess i j x) 4 (normalizedCubeMeasure R) := by
    intro i j
    exact (hq i j).1.mono_exponent (four_le_oneStepHarmonicExponent d hd)
  have hcoord : ∀ i j : Fin d,
      cubeLpNorm R 4 (fun x ↦ HR.hess i j x) ≤ ratio.toReal * B := by
    intro i j
    calc
      cubeLpNorm R 4 (fun x ↦ HR.hess i j x) ≤
          cubeLpNorm R (oneStepHarmonicExponent d hd).exponent
            (fun x ↦ HR.hess i j x) := by
        unfold cubeLpNorm
        apply ENNReal.toReal_mono (hq i j).1.eLpNorm_ne_top
        exact eLpNorm_le_eLpNorm_of_exponent_le
          (four_le_oneStepHarmonicExponent d hd)
      _ ≤ ratio.toReal * B := (hq i j).2
  unfold oneStepCellB
  calc
    cubeScaleFactor R * oneStepCellNormalizedHessianSize R HR ≤
        cubeScaleFactor R * oneStepCellHessianFourSize R HR :=
      mul_le_mul_of_nonneg_left
        (oneStepCellNormalizedHessianSize_le_hessianFourSize R HR hfour)
        (cubeScaleFactor_nonneg R)
    _ ≤ cubeScaleFactor R * ((d : ℝ) ^ 2 * (ratio.toReal * B)) := by
      apply mul_le_mul_of_nonneg_left _ (cubeScaleFactor_nonneg R)
      unfold oneStepCellHessianFourSize
      calc
        ∑ i : Fin d, ∑ j : Fin d, cubeLpNorm R 4 (fun x ↦ HR.hess i j x) ≤
            ∑ _i : Fin d, ∑ _j : Fin d, ratio.toReal * B :=
          Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hcoord i j
        _ = (d : ℝ) ^ 2 * (ratio.toReal * B) := by
          simp [nsmul_eq_mul]
          ring
    _ = cubeScaleFactor R * (d : ℝ) ^ 2 * ratio.toReal * B := by ring

/-- Source-facing arbitrary-center harmonic `B_z` package.  A cell may sit at
any center; it only has to lie in the transported half cube and in the fixed
concentric high-exponent region. -/
theorem exists_axisCube_harmonic_cellB_bound
    (d : ℕ) (hd : 3 ≤ d) :
    ∃ depth : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (z : Vec d) (L : ℝ), 0 < L →
        ∀ (u : H1Function (axisCube z L)),
          WeakPoissonEquationOn (axisCube z L) u (fun _ ↦ 0) →
          ∀ (R : TriadicCube d)
            (hRhalf : openCubeSet R ⊆ axisCubeInnerHalf z L)
            (_hRinner : openCubeSet R ⊆
              axisCube
                (CubeCalderonZygmund.axisCubeConcentricDepthCorner
                  z L (depth + 1))
                (CubeCalderonZygmund.axisCubeConcentricDepthSide
                  L (depth + 1))),
              ∃ uS : H1Function (axisCubeInnerHalf z L),
                uS.toFun = u.toFun ∧ uS.grad = u.grad ∧
                  ∃ H : HasWeakHessianOn (axisCubeInnerHalf z L) uS,
                    oneStepCellB R
                        (H.restrict (isOpen_openCubeSet R) hRhalf) ≤
                      cubeScaleFactor R * (d : ℝ) ^ 2 *
                        ((triadicAxisNormalizedMeasureRatio R
                          (CubeCalderonZygmund.axisCubeConcentricDepthSide
                            L (depth + 1))) ^
                          (1 / (oneStepHarmonicExponent d hd).exponent).toReal
                          ).toReal *
                        (C * L⁻¹ *
                          ∑ k : Fin d,
                            (eLpNorm (fun x ↦ u.grad x k) 2
                              (CubeCalderonZygmund.axisCubeNormalizedMeasure
                                z L)).toReal) := by
  obtain ⟨depth, C, hC, haxis⟩ :=
    exists_axisCube_harmonic_innerHalf_hessian_highExponent_bound d hd
  refine ⟨depth, C, hC, ?_⟩
  intro z L hL u hu R hRhalf hRinner
  obtain ⟨uS, huSfun, huSgrad, H, hhigh⟩ := haxis z L hL u hu
  refine ⟨uS, huSfun, huSgrad, H, ?_⟩
  exact oneStepCellB_le_of_axisCube_highExponent hd uS H R hRhalf
    (CubeCalderonZygmund.axisCubeConcentricDepthCorner z L (depth + 1))
    (CubeCalderonZygmund.axisCubeConcentricDepthSide L (depth + 1))
    (CubeCalderonZygmund.axisCubeConcentricDepthSide_pos hL _) hRinner
    (C * L⁻¹ * ∑ k : Fin d,
      (eLpNorm (fun x ↦ u.grad x k) 2
        (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)).toReal)
    hhigh

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
