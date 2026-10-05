module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryLocalizedSignedEnergy
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundarySupportAwareAbsorption

@[expose] public section

/-!
# Combined signed residual/lift cutoff pairing

The signed weak-energy identity leaves one common value factor and the flux
`a grad r + g + 2 a grad v`.  This file treats that flux as the corrected
flux of the genuine weak solution `r + 2 v`; it is never split by an absolute
value.

 this is the joint cutoff-product step in
`Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryAssemblyEnergy.lean`,
specialized to the scalar GMC corrected flux.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The residual plus twice a zero-force lift solves the residual equation. -/
theorem isDivFormWeakSolutionOn_add_two_smul_zero
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q : TriadicCube d) (r v : H1Function (openCubeSet Q))
    (g : Vec d → Vec d)
    (hr : IsDivFormWeakSolutionOn
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) (openCubeSet Q) r g)
    (hv : IsDivFormWeakSolutionOn
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) (openCubeSet Q) v (fun _ ↦ 0)) :
    IsDivFormWeakSolutionOn
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) (openCubeSet Q)
      (r + (2 : ℝ) • v) g := by
  intro phi
  let fr : Vec d → ℝ := fun x ↦
    vecDot ((_root_.SubdiffusiveProcess.Model.aCutoff M L omega x) • r.grad x)
      (phi.toH1Function.grad x)
  let fv : Vec d → ℝ := fun x ↦
    vecDot ((_root_.SubdiffusiveProcess.Model.aCutoff M L omega x) • v.grad x)
      (phi.toH1Function.grad x)
  have hfr : IntegrableOn fr (openCubeSet Q) := by
    exact integrableOn_vecDot_of_memVectorL2
      (memVectorL2_aCutoff_smul_grad M L omega Q r)
      phi.toH1Function.grad_memVectorL2
  have hfv : IntegrableOn fv (openCubeSet Q) := by
    exact integrableOn_vecDot_of_memVectorL2
      (memVectorL2_aCutoff_smul_grad M L omega Q v)
      phi.toH1Function.grad_memVectorL2
  have hpoint : (fun x ↦
      vecDot
        ((_root_.SubdiffusiveProcess.Model.aCutoff M L omega x) •
          (r + (2 : ℝ) • v).grad x)
        (phi.toH1Function.grad x)) = fun x ↦ fr x + 2 * fv x := by
    funext x
    simp only [H1Function.add_grad, H1Function.smul_grad, fr, fv,
      smul_add, smul_smul, vecDot_add_left, vecDot_smul_left]
    ring
  rw [hpoint, integral_add hfr (hfv.const_mul 2), integral_const_mul]
  rw [hr phi, hv phi]
  simp [vecDot]

/-- Pointwise, the two signed pairings are one corrected-flux pairing. -/
theorem boundaryCorrectedFluxCutoffPairingDensity_residual_add_two_lift
    (a eta w : Vec d → ℝ) (r v g : Vec d → Vec d) (x : Vec d) :
    boundaryCorrectedFluxCutoffPairingDensity a eta w r g x +
        2 * boundaryCorrectedFluxCutoffPairingDensity a eta w v (fun _ ↦ 0) x =
      boundaryCorrectedFluxCutoffPairingDensity a eta w
        (fun y ↦ r y + (2 : ℝ) • v y) g x := by
  simp only [boundaryCorrectedFluxCutoffPairingDensity, boundaryCorrectedFlux,
    add_zero, smul_add, vecDot_add_left, vecDot_smul_left]
  ring

/-- The coefficient energy of the combined flux solution is bounded by the
residual and lift energies with the literal `2` and `8` factors. -/
theorem cubeAverage_combinedFlux_energy_le_two_residual_add_eight_lift
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q : TriadicCube d) (r v : H1Function (openCubeSet Q)) :
    cubeAverage Q
        (coefficientEnergyDensity
          (publicCoeffField Q (aCutoffFamily M L omega))
          (r + (2 : ℝ) • v).grad) ≤
      2 * cubeAverage Q
          (coefficientEnergyDensity
            (publicCoeffField Q (aCutoffFamily M L omega)) r.grad) +
        8 * cubeAverage Q
          (coefficientEnergyDensity
            (publicCoeffField Q (aCutoffFamily M L omega)) v.grad) := by
  have hcube : volume.restrict (cubeSet Q) = volume.restrict (openCubeSet Q) :=
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q
  have hr : MemVectorL2 (cubeSet Q) r.grad := by
    rw [MemVectorL2, volumeMeasureOn, hcube]
    exact r.grad_memVectorL2
  have hv : MemVectorL2 (cubeSet Q) v.grad := by
    rw [MemVectorL2, volumeMeasureOn, hcube]
    exact v.grad_memVectorL2
  have hv2 : MemVectorL2 (cubeSet Q) ((2 : ℝ) • v).grad := by
    rw [MemVectorL2, volumeMeasureOn, hcube]
    exact ((2 : ℝ) • v).grad_memVectorL2
  have hsum : (r + (2 : ℝ) • v).grad =ᵐ[volume.restrict (cubeSet Q)]
      fun x ↦ r.grad x + ((2 : ℝ) • v).grad x := by
    filter_upwards with x
    rfl
  have hraw := cubeAverage_coefficientEnergyDensity_le_two_mul_add_of_ae_eq_add
    (publicCoeffField_isEllipticFieldOn_cubeSet Q (aCutoffFamily M L omega))
    (by
      rw [MemVectorL2, volumeMeasureOn, hcube]
      exact (r + (2 : ℝ) • v).grad_memVectorL2)
    hr hv2 hsum
  have hscale : cubeAverage Q
      (coefficientEnergyDensity
        (publicCoeffField Q (aCutoffFamily M L omega)) ((2 : ℝ) • v).grad) =
      4 * cubeAverage Q
        (coefficientEnergyDensity
          (publicCoeffField Q (aCutoffFamily M L omega)) v.grad) := by
    rw [← cubeAverage_const_mul]
    apply cubeAverage_eq_of_ae_eq_on_cubeSet
    filter_upwards with x
    unfold coefficientEnergyDensity
    simp only [H1Function.smul_grad, matVecMul_smul, vecDot_smul_left,
      vecDot_smul_right]
    ring
  rw [hscale] at hraw
  linarith only [hraw]

/-- Analytic finite-height cap for the two signed pairings, kept jointly all
the way through the corrected-flux estimate.  The three explicit energies
are precisely the residual, affine-lift, and residual-datum rows later
collapsed into the four manuscript budgets. -/
theorem exists_abs_combinedSignedPairing_weightedFiniteHeight
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
        (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
        {Q : TriadicCube d} {t : ℝ} {g : Vec d → Vec d}
        (r v hRes : H1Function (openCubeSet Q))
        (hweakR : IsDivFormWeakSolutionOn
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) (openCubeSet Q) r g)
        (hweakV : IsDivFormWeakSolutionOn
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) (openCubeSet Q) v (fun _ ↦ 0))
        {eta : Vec d → ℝ} {B Bcirc Kcirc A G : ℝ} (height : ℕ),
        0 < t → t < 1 / 2 → ForceBesovRegularity Q t (fun x ↦ -g x) →
        0 ≤ B → 0 ≤ Bcirc → 0 ≤ Kcirc → 0 ≤ A → 0 ≤ G →
        MemLp (scalarCutoffGradientField (fun y ↦ eta y ^ 2)) ∞
          (normalizedCubeMeasure Q) →
        (∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞)
          (fun x ↦ scalarCutoffGradientField (fun y ↦ eta y ^ 2) x i)) →
        (∀ i : Fin d, ∀ z ∈ cubeSet Q,
          ‖fderiv ℝ
              (fun x ↦ scalarCutoffGradientField (fun y ↦ eta y ^ 2) x i) z‖ ≤ B) →
        (∀ i : Fin d, ∀ N : ℕ,
          cubeBesovCircPartialNorm Q t (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
            (fun x ↦ (r - hRes).grad x i) ≤ Bcirc) →
        let Er := cubeAverage Q
          (coefficientEnergyDensity
            (publicCoeffField Q (aCutoffFamily M L omega)) r.grad)
        let Ev := cubeAverage Q
          (coefficientEnergyDensity
            (publicCoeffField Q (aCutoffFamily M L omega)) v.grad)
        let Eh := cubeAverage Q
          (coefficientEnergyDensity
            (publicCoeffField Q (aCutoffFamily M L omega)) hRes.grad)
        let Ew := cubeAverage Q
          (coefficientEnergyDensity
            (publicCoeffField Q (aCutoffFamily M L omega)) (r - hRes).grad)
        Bcirc = Kcirc * Real.sqrt Ew →
        weakFluxWithRHSRHS C Q (aCutoffFamily M L omega) t
              (fun x ↦ -g x)
              (forcedCubeSolutionOfDivForm_aCutoff M L omega Q
                (r + (2 : ℝ) • v) g
                (isDivFormWeakSolutionOn_add_two_smul_zero
                  M L omega Q r v g hweakR hweakV)) +
            boundaryNegativeToL2Factor (2 * t) *
              boundaryNormalizedEuclideanL2 Q (fun x ↦ -g x) ≤
          A * Real.sqrt (cubeAverage Q
            (coefficientEnergyDensity
              (publicCoeffField Q (aCutoffFamily M L omega))
              (r + (2 : ℝ) • v).grad)) + G →
        let xi := scalarCutoffGradientField (fun y ↦ eta y ^ 2)
        let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
        let Cfull := fullVectorPoincareCubeConstant Q
        let Kfine := cubeBesovScaleWeight (-(1 - t)) Q *
          ((Cfull * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Kcirc))
        let X₀ := cubeLpNorm Q (2 : ℝ≥0∞) (r - hRes).toFun
        let Xc := cubeLpNorm Q (2 : ℝ≥0∞)
          (cubeFluctuation Q (r - hRes).toFun)
        let mu := 2 * cubeLpNorm Q ∞ xi *
          boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height * Kfine
        let R := (d : ℝ) * cubeLpNorm Q ∞ xi * X₀ +
          2 * (cubeScaleFactor Q * B * (Gs * X₀) +
            cubeLpNorm Q ∞ xi *
              (boundaryFiniteHeightHeadGlobalCoeff t height * Xc))
        C * A * (Real.sqrt 2 * mu) ≤ 1 / 8 →
        |cubeAverage Q
            (boundaryCorrectedFluxCutoffPairingDensity
              (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta
              (r - hRes).toFun (r + (2 : ℝ) • v).grad g)| ≤
          (1 / 4 : ℝ) * Er + (1 / 2 : ℝ) * Ev +
            (1 / 8 : ℝ) * Eh +
            16 * (C * A * R) ^ 2 + 16 * (C * G * mu) ^ 2 + C * G * R := by
  obtain ⟨C, hC, hcap⟩ :=
    exists_abs_boundaryCorrectedFluxDensity_weightedFiniteHeight_combined d
  refine ⟨C, hC, ?_⟩
  intro M L omega Q t g r v hRes hweakR hweakV eta B Bcirc Kcirc A G height
    ht htHalf hreg hB hBcirc hKcirc hA hG hxiLp hxi hderiv hcirc
  dsimp only
  let Er := cubeAverage Q
    (coefficientEnergyDensity
      (publicCoeffField Q (aCutoffFamily M L omega)) r.grad)
  let Ev := cubeAverage Q
    (coefficientEnergyDensity
      (publicCoeffField Q (aCutoffFamily M L omega)) v.grad)
  let Eh := cubeAverage Q
    (coefficientEnergyDensity
      (publicCoeffField Q (aCutoffFamily M L omega)) hRes.grad)
  let Ew := cubeAverage Q
    (coefficientEnergyDensity
      (publicCoeffField Q (aCutoffFamily M L omega)) (r - hRes).grad)
  intro hBcircEq hweak
  let uComb := forcedCubeSolutionOfDivForm_aCutoff M L omega Q
    (r + (2 : ℝ) • v) g
    (isDivFormWeakSolutionOn_add_two_smul_zero
      M L omega Q r v g hweakR hweakV)
  have hEr : 0 ≤ Er := by
    dsimp [Er]
    exact cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn Q
      (publicCoeffField Q (aCutoffFamily M L omega)) r.grad
      (publicCoeffField_isEllipticFieldOn_cubeSet Q (aCutoffFamily M L omega))
  have hEv : 0 ≤ Ev := by
    dsimp [Ev]
    exact cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn Q
      (publicCoeffField Q (aCutoffFamily M L omega)) v.grad
      (publicCoeffField_isEllipticFieldOn_cubeSet Q (aCutoffFamily M L omega))
  have hEh : 0 ≤ Eh := by
    dsimp [Eh]
    exact cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn Q
      (publicCoeffField Q (aCutoffFamily M L omega)) hRes.grad
      (publicCoeffField_isEllipticFieldOn_cubeSet Q (aCutoffFamily M L omega))
  have hcomb : cubeAverage Q
      (coefficientEnergyDensity
        (publicCoeffField Q (aCutoffFamily M L omega)) uComb.toH1.grad) ≤
      2 * Er + 8 * Ev := by
    simpa only [uComb, forcedCubeSolutionOfDivForm_aCutoff_grad, Er, Ev] using!
      cubeAverage_combinedFlux_energy_le_two_residual_add_eight_lift
        M L omega Q r v
  have hvalue : Ew ≤ 2 * Er + 2 * Eh := by
    simpa only [Ew, Er, Eh] using!
      cubeAverage_coefficientEnergyDensity_h1Sub_le_two_mul_add Q
        (aCutoffFamily M L omega) r hRes
  let xi := scalarCutoffGradientField (fun y ↦ eta y ^ 2)
  let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
  let Cfull := fullVectorPoincareCubeConstant Q
  let Kfine := cubeBesovScaleWeight (-(1 - t)) Q *
    ((Cfull * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ((Fintype.card (Fin d) : ℝ) * Kcirc))
  let X₀ := cubeLpNorm Q (2 : ℝ≥0∞) (r - hRes).toFun
  let Xc := cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q (r - hRes).toFun)
  let mu := 2 * cubeLpNorm Q ∞ xi *
    boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height * Kfine
  let R := (d : ℝ) * cubeLpNorm Q ∞ xi * X₀ +
    2 * (cubeScaleFactor Q * B * (Gs * X₀) +
      cubeLpNorm Q ∞ xi * (boundaryFiniteHeightHeadGlobalCoeff t height * Xc))
  intro hsmall
  have hraw := hcap M L omega uComb (r - hRes)
    (eta := eta) (B := B) (Bcirc := Bcirc) (Kcirc := Kcirc)
    (A := A) (G := G) (Er := Er) (Ev := Ev) (Eh := Eh) height
    ht htHalf hreg hB hBcirc hKcirc hA hG hEr hEv hEh hxiLp hxi hderiv hcirc
  dsimp only at hraw
  have hraw' := hraw hBcircEq hcomb hvalue (by
    simpa only [uComb] using! hweak) hsmall
  simpa only [uComb, forcedCubeSolutionOfDivForm_aCutoff_grad,
    Er, Ev, Eh, xi, Gs, Cfull, Kfine, X₀, Xc, mu, R] using! hraw'

/-- The joint remainder is dominated by four copies of the standard common
Young envelope.  Hence all established finite descendant aggregation and
gap-power estimates remain reusable. -/
theorem combinedSignedYoungRemainder_le_four_standard
    {C A mu Eh R G : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hmu : 0 ≤ mu)
    (hR : 0 ≤ R) (hG : 0 ≤ G) :
    16 * (C * A * R) ^ 2 + 16 * (C * G * mu) ^ 2 + C * G * R ≤
      4 * (4 * (C * A * (Real.sqrt 2 * mu * Real.sqrt Eh + R)) ^ 2 +
        4 * (C * G * (Real.sqrt 2 * mu)) ^ 2 +
          C * G * (Real.sqrt 2 * mu * Real.sqrt Eh + R)) := by
  let Z := Real.sqrt 2 * mu * Real.sqrt Eh + R
  have hZ0 : 0 ≤ Z := by dsimp [Z]; positivity
  have hRZ : R ≤ Z := by
    dsimp [Z]
    exact le_add_of_nonneg_left
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hmu) (Real.sqrt_nonneg _))
  have hCA : 0 ≤ C * A := mul_nonneg hC hA
  have hCG : 0 ≤ C * G := mul_nonneg hC hG
  have hfirst : (C * A * R) ^ 2 ≤ (C * A * Z) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hCA hR)
      (mul_le_mul_of_nonneg_left hRZ hCA) 2
  have hsqrtTwoSq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsecond : (C * G * mu) ^ 2 ≤
      (C * G * (Real.sqrt 2 * mu)) ^ 2 := by
    have hsqrtTwo : 1 ≤ Real.sqrt 2 := by
      nlinarith [hsqrtTwoSq, Real.sqrt_nonneg 2]
    have hbase : C * G * mu ≤ C * G * (Real.sqrt 2 * mu) := by
      have hmu' : mu ≤ Real.sqrt 2 * mu := by
        simpa only [one_mul] using! mul_le_mul_of_nonneg_right hsqrtTwo hmu
      exact mul_le_mul_of_nonneg_left hmu' hCG
    exact pow_le_pow_left₀ (mul_nonneg hCG hmu) hbase 2
  have hcross : C * G * R ≤ C * G * Z :=
    mul_le_mul_of_nonneg_left hRZ hCG
  have hcross0 : 0 ≤ C * G * R := mul_nonneg hCG hR
  have hcrossZ0 : 0 ≤ C * G * Z := mul_nonneg hCG hZ0
  dsimp only [Z] at hfirst hcross ⊢
  nlinarith only [hfirst, hsecond, hcross, hcross0, hcrossZ0,
    sq_nonneg (C * A * (Real.sqrt 2 * mu * Real.sqrt Eh + R)),
    sq_nonneg (C * G * (Real.sqrt 2 * mu))]

/-- Parent finite-`2` caps price the combined signed product on one active
descendant.  The result has the same local factors as the established common
height argument, so its finite average can use that argument unchanged. -/
theorem exists_abs_combinedSignedPairing_descendant
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
        (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
        {Q R : TriadicCube d} {s sigma K : ℝ} {depth : ℕ}
        {g : Vec d → Vec d}
        (r v hRes : H1Function (openCubeSet R))
        (_hweakR : IsDivFormWeakSolutionOn
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) (openCubeSet R) r g)
        (_hweakV : IsDivFormWeakSolutionOn
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) (openCubeSet R) v (fun _ ↦ 0))
        {eta : Vec d → ℝ} {Bcut : ℝ} (height : ℕ),
        R ∈ descendantsAtDepth Q depth →
        0 < s → s ≤ 1 / 4 → 0 < sigma → 0 ≤ K →
        sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega) ≤ K →
        sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega))⁻¹ ≤ K →
        ForceBesovRegularity R (s / 3) (fun x ↦ -g x) →
        0 ≤ Bcut →
        MemLp (scalarCutoffGradientField (fun y ↦ eta y ^ 2)) ∞
          (normalizedCubeMeasure R) →
        (∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞)
          (fun x ↦ scalarCutoffGradientField (fun y ↦ eta y ^ 2) x i)) →
        (∀ i : Fin d, ∀ z ∈ cubeSet R,
          ‖fderiv ℝ
              (fun x ↦ scalarCutoffGradientField (fun y ↦ eta y ^ 2) x i) z‖ ≤
            Bcut) →
        let t := s / 3
        let W := Real.rpow (3 : ℝ) (2 * (s / 6) * (depth : ℝ))
        let Er := cubeAverage R
          (coefficientEnergyDensity
            (publicCoeffField R (aCutoffFamily M L omega)) r.grad)
        let Ev := cubeAverage R
          (coefficientEnergyDensity
            (publicCoeffField R (aCutoffFamily M L omega)) v.grad)
        let Eh := cubeAverage R
          (coefficientEnergyDensity
            (publicCoeffField R (aCutoffFamily M L omega)) hRes.grad)
        let Gsemi := scaleNormalizedPositiveBesovVectorSeminormTwo R t
          (fun x ↦ -g x)
        let Kcirc := cubeBesovScaleWeight (-t) R *
          ((geometricDiscount t 1)⁻¹ *
            ((d : ℝ) * Real.sqrt ((W * K) * sigma⁻¹)))
        let xi := scalarCutoffGradientField (fun y ↦ eta y ^ 2)
        let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
        let Kfine := cubeBesovScaleWeight (-(1 - t)) R *
          ((fullVectorPoincareCubeConstant R * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Kcirc))
        let X₀ := cubeLpNorm R (2 : ℝ≥0∞) (r - hRes).toFun
        let Xc := cubeLpNorm R (2 : ℝ≥0∞)
          (cubeFluctuation R (r - hRes).toFun)
        let mu := 2 * cubeLpNorm R ∞ xi *
          boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height * Kfine
        let rem := (d : ℝ) * cubeLpNorm R ∞ xi * X₀ +
          2 * (cubeScaleFactor R * Bcut * (Gs * X₀) +
            cubeLpNorm R ∞ xi *
              (boundaryFiniteHeightHeadGlobalCoeff t height * Xc))
        let Afac := C * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma)
        let Gfac := C * Real.rpow t (-(5 / 2 : ℝ)) *
            (Real.sqrt (W * K) * Real.sqrt sigma) *
            (Real.sqrt (W * K) * Real.sqrt sigma⁻¹) * Gsemi +
          boundaryNegativeToL2Factor (2 * t) *
            boundaryNormalizedEuclideanL2 R (fun x ↦ -g x)
        C * Afac * (Real.sqrt 2 * mu) ≤ 1 / 8 →
        |cubeAverage R
            (boundaryCorrectedFluxCutoffPairingDensity
              (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta
              (r - hRes).toFun (r + (2 : ℝ) • v).grad g)| ≤
          (1 / 4 : ℝ) * Er + (1 / 2 : ℝ) * Ev +
            (1 / 8 : ℝ) * Eh +
            16 * (C * Afac * rem) ^ 2 +
              16 * (C * Gfac * mu) ^ 2 + C * Gfac * rem := by
  obtain ⟨C, hC, hcap⟩ :=
    exists_abs_combinedSignedPairing_weightedFiniteHeight d
  refine ⟨C, hC, ?_⟩
  intro M L omega Q R s sigma K depth g r v hRes hweakR hweakV eta Bcut height
    hR hs hs4 hsigma hK hupper hlower hreg hBcut hxiLp hxi hderiv
  dsimp only
  let t := s / 3
  let W := Real.rpow (3 : ℝ) (2 * (s / 6) * (depth : ℝ))
  let Er := cubeAverage R
    (coefficientEnergyDensity
      (publicCoeffField R (aCutoffFamily M L omega)) r.grad)
  let Ev := cubeAverage R
    (coefficientEnergyDensity
      (publicCoeffField R (aCutoffFamily M L omega)) v.grad)
  let Eh := cubeAverage R
    (coefficientEnergyDensity
      (publicCoeffField R (aCutoffFamily M L omega)) hRes.grad)
  let Ew := cubeAverage R
    (coefficientEnergyDensity
      (publicCoeffField R (aCutoffFamily M L omega)) (r - hRes).grad)
  let Gsemi := scaleNormalizedPositiveBesovVectorSeminormTwo R t (fun x ↦ -g x)
  let Kcirc := cubeBesovScaleWeight (-t) R *
    ((geometricDiscount t 1)⁻¹ *
      ((d : ℝ) * Real.sqrt ((W * K) * sigma⁻¹)))
  let Bcirc := Kcirc * Real.sqrt Ew
  let xi := scalarCutoffGradientField (fun y ↦ eta y ^ 2)
  let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
  let Kfine := cubeBesovScaleWeight (-(1 - t)) R *
    ((fullVectorPoincareCubeConstant R * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ((Fintype.card (Fin d) : ℝ) * Kcirc))
  let X₀ := cubeLpNorm R (2 : ℝ≥0∞) (r - hRes).toFun
  let Xc := cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuation R (r - hRes).toFun)
  let mu := 2 * cubeLpNorm R ∞ xi *
    boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height * Kfine
  let rem := (d : ℝ) * cubeLpNorm R ∞ xi * X₀ +
    2 * (cubeScaleFactor R * Bcut * (Gs * X₀) +
      cubeLpNorm R ∞ xi * (boundaryFiniteHeightHeadGlobalCoeff t height * Xc))
  let Afac := C * t⁻¹ * (Real.sqrt (W * K) * Real.sqrt sigma)
  let Gfac := C * Real.rpow t (-(5 / 2 : ℝ)) *
      (Real.sqrt (W * K) * Real.sqrt sigma) *
      (Real.sqrt (W * K) * Real.sqrt sigma⁻¹) * Gsemi +
    boundaryNegativeToL2Factor (2 * t) *
      boundaryNormalizedEuclideanL2 R (fun x ↦ -g x)
  intro hsmall
  have ht : 0 < t := by dsimp [t]; positivity
  have htHalf : t < 1 / 2 := by dsimp [t]; linarith
  have hGsemi : 0 ≤ Gsemi := by
    dsimp [Gsemi, t]
    exact scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity hreg
  have hKcirc : 0 ≤ Kcirc := by
    dsimp [Kcirc]
    exact mul_nonneg (cubeBesovScaleWeight_nonneg (-t) R)
      (mul_nonneg
        (inv_nonneg.mpr (geometricDiscount_pos (mul_pos ht (by norm_num))).le)
        (mul_nonneg (by positivity) (Real.sqrt_nonneg _)))
  have hBcirc : 0 ≤ Bcirc := by
    dsimp [Bcirc]
    exact mul_nonneg hKcirc (Real.sqrt_nonneg _)
  have hcirc : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R t (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x ↦ (r - hRes).grad x i) ≤ Bcirc := by
    intro i N
    have hraw := aCutoff_h1Gradient_descendant_circPartialNorm_le_of_parent_sixth_cap
      M L omega (r - hRes) hR hs (by exact le_rfl)
        hsigma hlower i N
    simpa only [W, t, Kcirc, Bcirc, Ew, mul_assoc] using! hraw
  let uComb := forcedCubeSolutionOfDivForm_aCutoff M L omega R
    (r + (2 : ℝ) • v) g
    (isDivFormWeakSolutionOn_add_two_smul_zero
      M L omega R r v g hweakR hweakV)
  have hweakRaw := weakFluxWithRHSRHS_descendant_le_of_parent_sixth_caps
    uComb hR hC.le hs hsigma hK hupper hlower hreg (le_refl Gsemi)
  have hweak : weakFluxWithRHSRHS C R (aCutoffFamily M L omega) t
        (fun x ↦ -g x) uComb +
      boundaryNegativeToL2Factor (2 * t) *
        boundaryNormalizedEuclideanL2 R (fun x ↦ -g x) ≤
      Afac * Real.sqrt (cubeAverage R
        (coefficientEnergyDensity
          (publicCoeffField R (aCutoffFamily M L omega)) uComb.toH1.grad)) +
        Gfac := by
    have henergy : forcedSolutionEnergyNorm R (aCutoffFamily M L omega) uComb =
        Real.sqrt (cubeAverage R
          (coefficientEnergyDensity
            (publicCoeffField R (aCutoffFamily M L omega)) uComb.toH1.grad)) := by
      exact forcedSolutionEnergyNorm_eq_sqrt_cubeAverage_coefficientEnergyDensity_publicCoeffField
        R (aCutoffFamily M L omega) uComb
    rw [henergy] at hweakRaw
    dsimp only [W, t, Afac, Gfac, Gsemi] at hweakRaw ⊢
    linarith only [hweakRaw]
  have hAfac : 0 ≤ Afac := by dsimp [Afac]; positivity
  have hGfac : 0 ≤ Gfac := by
    dsimp [Gfac]
    exact add_nonneg (mul_nonneg (by positivity) hGsemi)
      (mul_nonneg (boundaryNegativeToL2Factor_nonneg _)
        (boundaryNormalizedEuclideanL2_nonneg R _))
  have hraw := hcap M L omega r v hRes hweakR hweakV
    (eta := eta) (B := Bcut) (Bcirc := Bcirc) (Kcirc := Kcirc)
    (A := Afac) (G := Gfac) height ht htHalf hreg hBcut hBcirc hKcirc
      hAfac hGfac hxiLp hxi hderiv hcirc
  have hraw' := hraw (by rfl) (by simpa only [uComb] using! hweak) hsmall
  simpa only [t, W, Er, Ev, Eh, Ew, Gsemi, Kcirc, Bcirc, xi, Gs,
    Kfine, X₀, Xc, mu, rem, Afac, Gfac] using! hraw'

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
