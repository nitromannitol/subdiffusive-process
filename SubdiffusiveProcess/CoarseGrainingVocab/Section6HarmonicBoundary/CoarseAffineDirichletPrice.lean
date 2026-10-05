module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryAffineCoarsePrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryASDSeparateDatum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCenteredForce
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEnergyReadout

@[expose] public section

/-!
# Coarse affine separation for the harmonic boundary datum

The affine mode of a boundary datum is lifted by the canonical symmetric
Dirichlet minimizer and is priced by the coarse finite-`2` upper ellipticity
quantity.  Only the centered remainder is sent through the positive-Besov
Dirichlet estimate.  Consequently the inverse power of the fractional order
does not multiply the mean slope.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch02 Homogenization.Book.Ch03 MeasureTheory
open Section6HarmonicApproximation

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The local coefficient-energy carrier is literally the normalized scalar
`aCutoff`-weighted gradient energy. -/
theorem localizedCoeffEnergyValue_aCutoffFamily_eq_volumeAverage
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) :
    localizedCoeffEnergyValue (openCubeSet Q)
        ((aCutoffFamily M L omega).coeffOn Q) u =
      volumeAverage (openCubeSet Q) (fun x ↦
        _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (u.grad x)) := by
  have h := localizedCoeffEnergyValue_aCutoffFamily_eq_translate
    M L omega Q 0 (openCubeSet Q) u u.grad (by simp)
  simpa using! h

/-- The sum of two zero-force Dirichlet solutions carries the sum of their
boundary data. -/
noncomputable def addZeroForceDirichletSolutions
    {Q : TriadicCube d} {a : CoeffFamily d}
    (v w : DirichletForcedCubeSolution Q a (fun _ ↦ 0)) :
    DirichletForcedCubeSolution Q a (fun _ ↦ 0) where
  toH1 := v.toH1 + w.toH1
  boundaryData := v.boundaryData + w.boundaryData
  weakSolution := isForcedEquation_add_zero v.weakSolution w.weakSolution
  zeroTraceDifference := by
    let rv := v.zeroTraceDifferenceH10
    let rw := w.zeroTraceDifferenceH10
    refine ⟨rv + rw, ?_⟩
    filter_upwards [v.zeroTraceDifferenceH10_toFun_ae_eq,
      w.zeroTraceDifferenceH10_toFun_ae_eq] with x hvx hwx
    change (rv.toH1Function + rw.toH1Function).toFun x = _
    simp only [H1Function.add_toFun]
    rw [hvx, hwx]
    ring

omit [NeZero d] in
@[simp] theorem addZeroForceDirichletSolutions_toH1
    {Q : TriadicCube d} {a : CoeffFamily d}
    (v w : DirichletForcedCubeSolution Q a (fun _ ↦ 0)) :
    (addZeroForceDirichletSolutions v w).toH1 = v.toH1 + w.toH1 :=
  rfl

omit [NeZero d] in
@[simp] theorem addZeroForceDirichletSolutions_boundaryData
    {Q : TriadicCube d} {a : CoeffFamily d}
    (v w : DirichletForcedCubeSolution Q a (fun _ ↦ 0)) :
    (addZeroForceDirichletSolutions v w).boundaryData =
      v.boundaryData + w.boundaryData :=
  rfl

private theorem localizedCoeffEnergyValue_add_le_two_mul_add
    (Q : TriadicCube d) (a : CoeffFamily d)
    (v w : H1Function (openCubeSet Q)) :
    localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) (v + w) ≤
      2 * localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) v +
        2 * localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) w := by
  have hsum : (v + w).grad =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x ↦ v.grad x + w.grad x := by
    filter_upwards with x
    exact congrFun (H1Function.add_grad v w) x
  have htriangle :=
    volumeAverage_coefficientEnergyDensity_le_two_mul_add_of_ae_eq_add
      (V := openCubeSet Q) (A := publicCoeffField Q a)
      (lam := (a.coeffOn Q).lam) (Lam := (a.coeffOn Q).Lam)
      ((publicCoeffField_isEllipticFieldOn_cubeSet Q a).mono
        (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q))
      (v + w).grad_memVectorL2 v.grad_memVectorL2 w.grad_memVectorL2 hsum
  rw [localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
      (Set.Subset.rfl) (v + w),
    localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
      (Set.Subset.rfl) v,
    localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
      (Set.Subset.rfl) w]
  exact htriangle

private theorem lambdaS_mul_lowerFactor_energyNorm_sq
    (Q : TriadicCube d) (a : CoeffFamily d) {t : ℝ} (ht : 0 < t)
    (w : DirichletForcedCubeSolution Q a (fun _ ↦ 0)) :
    Ch02.lambdaS Q t a *
        (poincareLowerEllipticityFactor Q a t (.finite 1) *
          dirichletForcedSolutionEnergyNorm Q a w) ^ 2 =
      localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) w.toH1 := by
  have hlam : 0 < Ch02.lambdaS Q t a :=
    Ch02.lambdaSq_finite_pos Q a ht (by norm_num)
  have hlowerSq :
      (poincareLowerEllipticityFactor Q a t (.finite 1)) ^ 2 =
        (Ch02.lambdaS Q t a)⁻¹ := by
    unfold poincareLowerEllipticityFactor Ch02.lambdaS
    calc
      (Real.rpow (Ch02.lambdaSq Q t (.finite 1) a) (-(1 / 2 : ℝ))) ^ 2 =
          Real.rpow
            (Real.rpow (Ch02.lambdaSq Q t (.finite 1) a) (-(1 / 2 : ℝ)))
            (2 : ℝ) := (Real.rpow_two _).symm
      _ = Real.rpow (Ch02.lambdaSq Q t (.finite 1) a)
          (-(1 / 2 : ℝ) * (2 : ℝ)) :=
        (Real.rpow_mul hlam.le _ _).symm
      _ = Real.rpow (Ch02.lambdaSq Q t (.finite 1) a) (-1 : ℝ) := by norm_num
      _ = (Ch02.lambdaSq Q t (.finite 1) a)⁻¹ := Real.rpow_neg_one _
  rw [mul_pow, hlowerSq]
  field_simp [hlam.ne']
  exact dirichletForcedSolutionEnergyNorm_sq Q a w

/-- A harmonic lift of a general boundary datum, with the affine mean priced
by the coarse finite-`2` matrix cap and only the centered fluctuation charged
to the positive-Besov datum budget. -/
theorem exists_coarseAffineDirichletLift_energy_le (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
        (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (Q : TriadicCube d) {s sigma B : ℝ}
        (h : H1Function (openCubeSet Q)),
        0 < s → s ≤ 1 / 4 → 0 < sigma → 0 ≤ B →
        sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega) ≤ B →
        Ch02.LambdaS Q (s / 2) (aCutoffFamily M L omega) ≤ B * sigma →
        ForceBesovRegularity Q s h.grad →
        ∃ v : DirichletForcedCubeSolution Q
            (aCutoffFamily M L omega) (fun _ ↦ 0),
          v.boundaryData = h ∧
          localizedCoeffEnergyValue (openCubeSet Q)
              ((aCutoffFamily M L omega).coeffOn Q) v.toH1 ≤
            C * B * sigma *
              (vecNormSq (cubeAverageVec Q h.grad) +
                Real.rpow (s / 2) (-3 : ℝ) *
                  scaleNormalizedPositiveBesovVectorSeminormTwo Q s h.grad ^ 2) := by
  obtain ⟨Cdatum, hCdatum, hdatum⟩ :=
    exists_lambdaS_mul_zeroForceDatumEnergy_sq_le d
  refine ⟨2 * max 1 Cdatum, by positivity, ?_⟩
  intro M L omega Q s sigma B h hs hs4 hsigma hB hupper hLambda hreg
  let p : Vec d := cubeAverageVec Q h.grad
  let ell : H1Function (openCubeSet Q) :=
    H1Function.affineOnIsSobolevRegularDomain
      (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain p
  let hRes : H1Function (openCubeSet Q) := h - ell
  obtain ⟨vAffine, hvAffineDatum, hvAffineEnergy⟩ :=
    exists_aCutoffAffineDirichletLift_energy_le_normalizedCap
      M L omega Q (by linarith only [hs]) hsigma hupper p
  obtain ⟨vRes, hvResDatum, _hvResMinimal⟩ :=
    exists_aCutoffZeroForceDirichletLift_energy_le M L omega Q hRes
  have hResGrad : hRes.grad = cubeFluctuationVec Q h.grad := by
    funext x
    simp only [hRes, ell, H1Function.sub_grad,
      H1Function.affineOnIsSobolevRegularDomain_grad]
    rfl
  have hResReg : ForceBesovRegularity Q s hRes.grad := by
    rw [hResGrad]
    exact forceBesovRegularity_cubeFluctuationVec hreg
  have haverage : cubeAverageVec Q hRes.grad = 0 := by
    rw [hResGrad]
    change cubeAverageVec Q (fun x ↦ h.grad x - cubeAverageVec Q h.grad) = 0
    rw [cubeAverageVec_sub_const Q h.grad (cubeAverageVec Q h.grad) hreg.memLp]
    exact sub_self _
  have hResNorm : scaleNormalizedPositiveBesovVectorNormTwo Q s hRes.grad =
      scaleNormalizedPositiveBesovVectorSeminormTwo Q s h.grad := by
    unfold scaleNormalizedPositiveBesovVectorNormTwo
    rw [haverage]
    have hzero : vecNormSq (0 : Vec d) = 0 := by simp [vecNormSq, vecDot]
    rw [hzero, Real.sqrt_zero, zero_add, hResGrad,
      scaleNormalizedPositiveBesovVectorSeminormTwo_cubeFluctuationVec hreg]
  have hResReg' : ForceBesovRegularity Q (2 * (s / 2)) hRes.grad := by
    simpa [show 2 * (s / 2) = s by ring] using! hResReg
  have hResRaw := hdatum (t := s / 2) vRes hRes hvResDatum
    (by linarith only [hs]) (by linarith only [hs4]) hResReg'
  have htwoHalf : 2 * (s / 2) = s := by ring
  rw [lambdaS_mul_lowerFactor_energyNorm_sq Q
      (aCutoffFamily M L omega) (by linarith only [hs]) vRes,
    htwoHalf, hResNorm] at hResRaw
  have hResEnergy : localizedCoeffEnergyValue (openCubeSet Q)
        ((aCutoffFamily M L omega).coeffOn Q) vRes.toH1 ≤
      Cdatum * (Real.rpow (s / 2) (-3 : ℝ) * (B * sigma) *
        scaleNormalizedPositiveBesovVectorSeminormTwo Q s h.grad ^ 2) := by
    apply hResRaw.trans
    have hsemi0 : 0 ≤
        scaleNormalizedPositiveBesovVectorSeminormTwo Q s h.grad ^ 2 := sq_nonneg _
    have hpow0 : 0 ≤ Real.rpow (s / 2) (-3 : ℝ) :=
      Real.rpow_nonneg (by positivity) _
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hLambda hpow0) hsemi0) hCdatum.le
  let v := addZeroForceDirichletSolutions vAffine vRes
  have hvDatum : v.boundaryData = h := by
    dsimp [v]
    rw [hvAffineDatum, hvResDatum]
    change ell + hRes = h
    dsimp only [hRes]
    abel
  have hvSplit := localizedCoeffEnergyValue_add_le_two_mul_add Q
    (aCutoffFamily M L omega) vAffine.toH1 vRes.toH1
  have hBsig0 : 0 ≤ B * sigma := mul_nonneg hB hsigma.le
  have hmean0 : 0 ≤ vecNormSq p := vecNormSq_nonneg p
  have hfluct0 : 0 ≤ Real.rpow (s / 2) (-3 : ℝ) *
      scaleNormalizedPositiveBesovVectorSeminormTwo Q s h.grad ^ 2 :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)
  refine ⟨v, hvDatum, ?_⟩
  calc
    localizedCoeffEnergyValue (openCubeSet Q)
        ((aCutoffFamily M L omega).coeffOn Q) v.toH1 ≤
      2 * localizedCoeffEnergyValue (openCubeSet Q)
          ((aCutoffFamily M L omega).coeffOn Q) vAffine.toH1 +
        2 * localizedCoeffEnergyValue (openCubeSet Q)
          ((aCutoffFamily M L omega).coeffOn Q) vRes.toH1 := by
            simpa only [v, addZeroForceDirichletSolutions_toH1] using! hvSplit
    _ ≤ 2 * (B * sigma * vecNormSq p) +
        2 * (Cdatum * (Real.rpow (s / 2) (-3 : ℝ) * (B * sigma) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q s h.grad ^ 2)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hvAffineEnergy (by norm_num))
        (mul_le_mul_of_nonneg_left hResEnergy (by norm_num))
    _ ≤ 2 * max 1 Cdatum * (B * sigma) *
        (vecNormSq p + Real.rpow (s / 2) (-3 : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q s h.grad ^ 2) := by
      have hCmean : 1 ≤ max 1 Cdatum := le_max_left _ _
      have hCfluct : Cdatum ≤ max 1 Cdatum := le_max_right _ _
      have hmeanBound :
          2 * (B * sigma * vecNormSq p) ≤
            2 * (max 1 Cdatum * (B * sigma) * vecNormSq p) := by
        have hcoefBound := mul_le_mul_of_nonneg_right hCmean
          (mul_nonneg hBsig0 hmean0)
        calc
          2 * (B * sigma * vecNormSq p) =
              2 * (1 * ((B * sigma) * vecNormSq p)) := by ring
          _ ≤ 2 * (max 1 Cdatum * ((B * sigma) * vecNormSq p)) :=
            mul_le_mul_of_nonneg_left hcoefBound (by norm_num)
          _ = _ := by ring
      have hfluctBound :
          2 * (Cdatum * (Real.rpow (s / 2) (-3 : ℝ) * (B * sigma) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q s h.grad ^ 2)) ≤
            2 * (max 1 Cdatum * (B * sigma) *
              (Real.rpow (s / 2) (-3 : ℝ) *
                scaleNormalizedPositiveBesovVectorSeminormTwo Q s h.grad ^ 2)) := by
        have hcoefBound := mul_le_mul_of_nonneg_right hCfluct
          (mul_nonneg hBsig0 hfluct0)
        calc
          2 * (Cdatum * (Real.rpow (s / 2) (-3 : ℝ) * (B * sigma) *
              scaleNormalizedPositiveBesovVectorSeminormTwo Q s h.grad ^ 2)) =
              2 * (Cdatum * ((B * sigma) *
                (Real.rpow (s / 2) (-3 : ℝ) *
                  scaleNormalizedPositiveBesovVectorSeminormTwo Q s h.grad ^ 2))) := by
            ring
          _ ≤ 2 * (max 1 Cdatum * ((B * sigma) *
                (Real.rpow (s / 2) (-3 : ℝ) *
                  scaleNormalizedPositiveBesovVectorSeminormTwo Q s h.grad ^ 2))) :=
            mul_le_mul_of_nonneg_left hcoefBound (by norm_num)
          _ = _ := by ring
      calc
        _ ≤ 2 * (max 1 Cdatum * (B * sigma) * vecNormSq p) +
            2 * (max 1 Cdatum * (B * sigma) *
              (Real.rpow (s / 2) (-3 : ℝ) *
                scaleNormalizedPositiveBesovVectorSeminormTwo Q s h.grad ^ 2)) :=
          add_le_add hmeanBound hfluctBound
        _ = _ := by ring
    _ = 2 * max 1 Cdatum * B * sigma *
        (vecNormSq (cubeAverageVec Q h.grad) +
          Real.rpow (s / 2) (-3 : ℝ) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q s h.grad ^ 2) := by
      dsimp [p]
      ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
