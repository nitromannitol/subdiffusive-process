module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov.JBoundByBesov
public import Homogenization.Besov.Duality.CaccioppoliVectorization
public import Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.Geometry

@[expose] public section

namespace SubdiffusiveProcess.Besov
open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov
open scoped BigOperators ENNReal ContDiff
noncomputable section
variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The normalized scalar L2 norm, in integral form. -/
theorem cubeLpNorm_two_sq_eq_integral [_instNeZero : NeZero d] (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    cubeLpNorm Q 2 f ^ 2 = ∫ x, f x ^ 2 ∂normalizedCubeMeasure Q := by
  rw [← Ch03.normalizedL2SqOnSet_openCubeSet_eq_cubeLpNorm_two_sq Q f hf,
    ← cubeAverage_eq_integral_normalizedCubeMeasure]
  unfold Ch03.normalizedL2SqOnSet Ch03.normalizedSetAverage volumeAverage cubeAverage
  rw [volume_openCubeSet_toReal, setIntegral_cubeSet_eq_setIntegral_openCubeSet]

/-- Smooth scalar coordinates as weak Sobolev functions on the open cube. -/
def smoothCoordinate (Q : TriadicCube d) (φ : Vec d → Vec d)
    (hφ : ContDiff ℝ ∞ φ) (i : Fin d) : W1pFunction (openCubeSet Q) 2 :=
  W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_openCubeSet Q) ((contDiff_pi.mp hφ i).of_le (by simp))

omit [NeZero d] in
@[simp] theorem smoothCoordinate_toFun [_instNeZero : NeZero d] (Q : TriadicCube d) (φ : Vec d → Vec d)
    (hφ : ContDiff ℝ ∞ φ) (i : Fin d) :
    (smoothCoordinate Q φ hφ i).toFun = fun x => φ x i := rfl

omit [NeZero d] in
@[simp] theorem smoothCoordinate_grad [_instNeZero : NeZero d] (Q : TriadicCube d) (φ : Vec d → Vec d)
    (hφ : ContDiff ℝ ∞ φ) (i j : Fin d) (x : Vec d) :
    (smoothCoordinate Q φ hφ i).grad x j = fderiv ℝ φ x (Pi.single j 1) i := by
  change fderiv ℝ (fun y => φ y i) x (basisVec j) = _
  have hpi := fderiv_pi (fun k : Fin d =>
    ((contDiff_pi.mp hφ k).differentiable (by simp)).differentiableAt (x := x))
  have h := congrArg (fun A => A (Pi.single j 1) i) hpi
  simpa only [ContinuousLinearMap.pi_apply, basisVec] using h.symm

omit [NeZero d] in
theorem smoothCoordinate_memLp [_instNeZero : NeZero d] (Q : TriadicCube d) (φ : Vec d → Vec d)
    (hφ : ContDiff ℝ ∞ φ) (i : Fin d) :
    MemLp (fun x => φ x i) 2 (normalizedCubeMeasure Q) := by
  rw [← openCubeSet_boundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
  exact (((isOpenBoundedConvexDomain_openCubeSet Q).toBoundedMeasurableDomain
    (Ch02.openCubeSet_nonempty Q)).memLp_normalizedVolume_iff _ _).mpr
      (smoothCoordinate Q φ hφ i).memLp

theorem smoothDerivative_memLp (Q : TriadicCube d) (φ : Vec d → Vec d)
    (hφ : ContDiff ℝ ∞ φ) (i j : Fin d) :
    MemLp (fun x => fderiv ℝ φ x (Pi.single j 1) i) 2 (normalizedCubeMeasure Q) := by
  rw [← openCubeSet_boundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
  refine (((isOpenBoundedConvexDomain_openCubeSet Q).toBoundedMeasurableDomain
    (Ch02.openCubeSet_nonempty Q)).memLp_normalizedVolume_iff _ _).mpr ?_
  simpa only [smoothCoordinate_grad] using! (smoothCoordinate Q φ hφ i).gradMemLp j

noncomputable def smoothTestGradientSize (Q : TriadicCube d) (φ : Vec d → Vec d) : ℝ :=
  Real.sqrt (∫ x, ∑ i : Fin d, ∑ j : Fin d,
    (fderiv ℝ φ x (Pi.single j 1) i) ^ 2 ∂normalizedCubeMeasure Q)

noncomputable def smoothTestValueSize (Q : TriadicCube d) (φ : Vec d → Vec d) : ℝ :=
  Real.sqrt (∫ x, vecNormSq (φ x) ∂normalizedCubeMeasure Q)

noncomputable def smoothTestSize (Q : TriadicCube d) (φ : Vec d → Vec d) : ℝ :=
  smoothTestGradientSize Q φ + (cubeScaleFactor Q)⁻¹ * smoothTestValueSize Q φ

/-- Each coordinate gradient is bounded by the Frobenius gradient norm. -/
theorem smoothCoordinate_gradientSize_le (Q : TriadicCube d) (φ : Vec d → Vec d)
    (hφ : ContDiff ℝ ∞ φ) (i : Fin d) :
    cubeLpNorm Q 2 (fun x => euclideanNorm ((smoothCoordinate Q φ hφ i).grad x)) ≤
      smoothTestGradientSize Q φ := by
  let u := smoothCoordinate Q φ hφ i
  have hu : MemLp (fun x => euclideanNorm (u.grad x)) 2 (normalizedCubeMeasure Q) := by
    rw [← openCubeSet_boundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
    exact u.gradEuclideanMemLp
      ((isOpenBoundedConvexDomain_openCubeSet Q).toBoundedMeasurableDomain
        (Ch02.openCubeSet_nonempty Q)) 2
  have hInt : Integrable (fun x => ∑ k : Fin d, ∑ j : Fin d,
      (fderiv ℝ φ x (Pi.single j 1) k) ^ 2) (normalizedCubeMeasure Q) := by
    exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ =>
      (smoothDerivative_memLp Q φ hφ k j).integrable_sq
  have hsq : cubeLpNorm Q 2 (fun x => euclideanNorm (u.grad x)) ^ 2 ≤
      ∫ x, ∑ k : Fin d, ∑ j : Fin d,
        (fderiv ℝ φ x (Pi.single j 1) k) ^ 2 ∂normalizedCubeMeasure Q := by
    rw [cubeLpNorm_two_sq_eq_integral Q _ hu]
    refine integral_mono hu.integrable_sq hInt ?_
    intro x
    dsimp only
    rw [euclideanNorm_sq]
    simp only [vecNormSq, vecDot, ← pow_two]
    change (∑ j : Fin d, (u.grad x j) ^ 2) ≤ _
    simp only [u, smoothCoordinate_grad]
    exact Finset.single_le_sum
      (f := fun k : Fin d => ∑ j : Fin d, (fderiv ℝ φ x (Pi.single j 1) k) ^ 2)
      (fun k _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ i)
  calc
    cubeLpNorm Q 2 (fun x => euclideanNorm (u.grad x)) =
        Real.sqrt (cubeLpNorm Q 2 (fun x => euclideanNorm (u.grad x)) ^ 2) :=
      (Real.sqrt_sq (cubeLpNorm_nonneg Q _ _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt hsq

/-- Each coordinate value is bounded by the Euclidean vector norm. -/
theorem smoothCoordinate_valueSize_le (Q : TriadicCube d) (φ : Vec d → Vec d)
    (hφ : ContDiff ℝ ∞ φ) (i : Fin d) :
    cubeLpNorm Q 2 (fun x => φ x i) ≤ smoothTestValueSize Q φ := by
  have hInt : Integrable (fun x => vecNormSq (φ x)) (normalizedCubeMeasure Q) := by
    simpa only [vecNormSq, vecDot, ← pow_two] using
      (integrable_finsetSum Finset.univ fun j _ => (smoothCoordinate_memLp Q φ hφ j).integrable_sq)
  have hsq : cubeLpNorm Q 2 (fun x => φ x i) ^ 2 ≤
      ∫ x, vecNormSq (φ x) ∂normalizedCubeMeasure Q := by
    rw [cubeLpNorm_two_sq_eq_integral Q _ (smoothCoordinate_memLp Q φ hφ i)]
    refine integral_mono (smoothCoordinate_memLp Q φ hφ i).integrable_sq hInt ?_
    intro x
    dsimp only
    simp only [vecNormSq, vecDot, ← pow_two]
    change φ x i ^ 2 ≤ ∑ j : Fin d, φ x j ^ 2
    exact Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  calc
    cubeLpNorm Q 2 (fun x => φ x i) = Real.sqrt (cubeLpNorm Q 2 (fun x => φ x i) ^ 2) :=
      (Real.sqrt_sq (cubeLpNorm_nonneg Q _ _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt hsq

/-- Smooth test coordinates lie in a dimension-uniform full positive Besov ball. -/
theorem smoothCoordinate_dualTestNorm_le (Q : TriadicCube d) (φ : Vec d → Vec d)
    (hφ : ContDiff ℝ ∞ φ) (i : Fin d) (N : ℕ) :
    cubeBesovDualTestNorm Q 1 2 1 N (fun x => φ x i) ≤
      cubeMeanZeroHMinusOneBesovTestConstant d * smoothTestSize Q φ := by
  have hp : cubeBesovConjExponent 2 = 2 := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  rw [cubeBesovDualTestNorm_of_conjExponent_eq_top _ _ _ _ _ _ cubeBesovConjExponent_one,
    hp, cubeBesovPartialNormTop]
  have hgrad := cubeBesovPartialSeminormTop_one_two_le_normalizedW1pSeminorm Q N
    (smoothCoordinate Q φ hφ i)
  rw [openCubeSet_normalizedW1pSeminorm_two_eq_cubeLpNorm_euclideanGrad] at hgrad
  have hv := norm_cubeAverage_le_cubeLpNorm_two Q _ (smoothCoordinate_memLp Q φ hφ i)
  have hg : cubeBesovPartialSeminormTop Q 1 2 N (fun x => φ x i) ≤
      cubeBesovW12EmbeddingConstant d * smoothTestGradientSize Q φ :=
    hgrad.trans (mul_le_mul_of_nonneg_left (smoothCoordinate_gradientSize_le Q φ hφ i)
      (cubeBesovW12EmbeddingConstant_nonneg d))
  have hv' := hv.trans (smoothCoordinate_valueSize_le Q φ hφ i)
  have hw : cubeBesovScaleWeight 1 Q = (cubeScaleFactor Q)⁻¹ := by
    simp only [cubeBesovScaleWeight, Real.rpow_neg_one]
  rw [hw]
  have hscale : 0 ≤ (cubeScaleFactor Q)⁻¹ := inv_nonneg.mpr (by unfold cubeScaleFactor; positivity)
  have hval := mul_le_mul_of_nonneg_left hv' hscale
  unfold cubeMeanZeroHMinusOneBesovTestConstant smoothTestSize
  have hG : 0 ≤ smoothTestGradientSize Q φ := Real.sqrt_nonneg _
  have hV : 0 ≤ smoothTestValueSize Q φ := Real.sqrt_nonneg _
  nlinarith [cubeBesovW12EmbeddingConstant_nonneg d, mul_nonneg hscale hV,
    mul_nonneg (cubeBesovW12EmbeddingConstant_nonneg d) (mul_nonneg hscale hV)]

end
end SubdiffusiveProcess.Besov
