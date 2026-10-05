module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundarySupportAwareAbsorption
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryDescendantEllipticity

@[expose] public section

/-!
# Good-event pricing of the support-aware descendant estimate

This module composes the uncentered finite-height cutoff product with the
finite-`2` ellipticity caps localized from a parent cube.  It is the local
active-cell estimate required by the annular descendant summation: no support
or childwise centering hypothesis occurs.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The scalar GMC weak equation is the public Chapter-3 forced equation
with forcing `-g`.  This adapter is deliberately on the full parent cube;
`restrictForcedCubeSolutionToDescendant` then supplies every child read. -/
noncomputable def forcedCubeSolutionOfDivForm_aCutoff
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    (g : Vec d → Vec d)
    (hweak : IsDivFormWeakSolutionOn
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) (openCubeSet Q) u g) :
    ForcedCubeSolution Q (aCutoffFamily M L omega) (fun x ↦ -g x) where
  toH1 := u
  weakSolution := by
    intro phi
    calc
      ∫ x in openCubeSet Q,
          vecDot
            (matVecMul
              (((aCutoffFamily M L omega).coeffOn Q).toCoeffField x) (u.grad x))
            (phi.toH1Function.grad x) ∂volume =
        ∫ x in openCubeSet Q,
          vecDot ((_root_.SubdiffusiveProcess.Model.aCutoff M L omega x) • u.grad x)
            (phi.toH1Function.grad x) ∂volume := by
              apply integral_congr_ae
              filter_upwards with x
              simp only [aCutoffFamily, aCutoffTriadicData,
                ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
                ScalarCoeffOnData.toCoeffOn, scalarCoeffField, matVecMul_scalarMatrix]
      _ = -∫ x in openCubeSet Q,
          vecDot (g x) (phi.toH1Function.grad x) ∂volume := hweak phi
      _ = ∫ x in openCubeSet Q,
          vecDot (-g x) (phi.toH1Function.grad x) ∂volume := by
            rw [← integral_neg]
            apply integral_congr_ae
            filter_upwards with x
            simp only [vecDot_neg_left]

@[simp] theorem forcedCubeSolutionOfDivForm_aCutoff_toFun
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    (g : Vec d → Vec d)
    (hweak : IsDivFormWeakSolutionOn
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) (openCubeSet Q) u g) :
    (forcedCubeSolutionOfDivForm_aCutoff M L omega Q u g hweak).toH1.toFun = u.toFun :=
  rfl

@[simp] theorem forcedCubeSolutionOfDivForm_aCutoff_grad
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    (g : Vec d → Vec d)
    (hweak : IsDivFormWeakSolutionOn
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) (openCubeSet Q) u g) :
    (forcedCubeSolutionOfDivForm_aCutoff M L omega Q u g hweak).toH1.grad = u.grad :=
  rfl

/-- The support-aware one-quarter estimate on a descendant, with both the
weak-flux and arbitrary-boundary circ factors priced by the parent's
finite-`2` caps.  This is the local theorem summed by
`boundaryCrossScaleEnergyProfile_oneThird_le_of_adaptiveLocalCells`. -/
theorem exists_abs_boundaryCorrectedFluxDensity_descendant_quarter
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
        (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
        {Q R : TriadicCube d} {s sigma K : ℝ} {depth : ℕ}
        {g₀ : Vec d → Vec d}
        (u : ForcedCubeSolution R (aCutoffFamily M L omega) (fun x ↦ -g₀ x))
        (w : H1Function (openCubeSet R))
        {eta : Vec d → ℝ} {Bcut Eh : ℝ} (height : ℕ),
        R ∈ descendantsAtDepth Q depth →
        0 < s → s ≤ 1 / 4 → 0 < sigma → 0 ≤ K →
        sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega) ≤ K →
        sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega))⁻¹ ≤ K →
        ForceBesovRegularity R (s / 3) (fun x ↦ -g₀ x) →
        0 ≤ Bcut → 0 ≤ Eh →
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
        let Eu := cubeAverage R
          (coefficientEnergyDensity
            (publicCoeffField R (aCutoffFamily M L omega)) u.toH1.grad)
        let Ew := cubeAverage R
          (coefficientEnergyDensity
            (publicCoeffField R (aCutoffFamily M L omega)) w.grad)
        let Gsemi := scaleNormalizedPositiveBesovVectorSeminormTwo R t
          (fun x ↦ -g₀ x)
        let Kcirc := cubeBesovScaleWeight (-t) R *
          ((geometricDiscount t 1)⁻¹ *
            ((d : ℝ) * Real.sqrt ((W * K) * sigma⁻¹)))
        let xi := scalarCutoffGradientField (fun y ↦ eta y ^ 2)
        let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
        let Kfine := cubeBesovScaleWeight (-(1 - t)) R *
          ((fullVectorPoincareCubeConstant R * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Kcirc))
        let X₀ := cubeLpNorm R (2 : ℝ≥0∞) w.toFun
        let Xc := cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuation R w.toFun)
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
            boundaryNormalizedEuclideanL2 R (fun x ↦ -g₀ x)
        Ew ≤ 2 * Eu + 2 * Eh →
        C * Afac * (Real.sqrt 2 * mu) ≤ 1 / 8 →
        |cubeAverage R
            (boundaryCorrectedFluxCutoffPairingDensity
              (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta
              w.toFun u.toH1.grad g₀)| ≤
          (1 / 4 : ℝ) * Eu +
            4 * (C * Afac * (Real.sqrt 2 * mu * Real.sqrt Eh + rem)) ^ 2 +
            4 * (C * Gfac * (Real.sqrt 2 * mu)) ^ 2 +
              C * Gfac * (Real.sqrt 2 * mu * Real.sqrt Eh + rem) := by
  obtain ⟨C, hC, hquarter⟩ :=
    exists_abs_boundaryCorrectedFluxDensity_weightedFiniteHeight_quarter d
  refine ⟨C, hC, ?_⟩
  intro M L omega Q R s sigma K depth g₀ u w eta Bcut Eh height hR hs hs4
    hsigma hK hupper hlower hg hBcut hEh hxiLp hxi hderiv
  dsimp only
  let t := s / 3
  let W := Real.rpow (3 : ℝ) (2 * (s / 6) * (depth : ℝ))
  let Eu := cubeAverage R
    (coefficientEnergyDensity
      (publicCoeffField R (aCutoffFamily M L omega)) u.toH1.grad)
  let Ew := cubeAverage R
    (coefficientEnergyDensity
      (publicCoeffField R (aCutoffFamily M L omega)) w.grad)
  let Gsemi := scaleNormalizedPositiveBesovVectorSeminormTwo R t (fun x ↦ -g₀ x)
  let Kcirc := cubeBesovScaleWeight (-t) R *
    ((geometricDiscount t 1)⁻¹ *
      ((d : ℝ) * Real.sqrt ((W * K) * sigma⁻¹)))
  let Bcirc := Kcirc * Real.sqrt Ew
  let xi := scalarCutoffGradientField (fun y ↦ eta y ^ 2)
  let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
  let Kfine := cubeBesovScaleWeight (-(1 - t)) R *
    ((fullVectorPoincareCubeConstant R * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ((Fintype.card (Fin d) : ℝ) * Kcirc))
  let X₀ := cubeLpNorm R (2 : ℝ≥0∞) w.toFun
  let Xc := cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuation R w.toFun)
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
      boundaryNormalizedEuclideanL2 R (fun x ↦ -g₀ x)
  intro hsplit hsmall
  have ht : 0 < t := by dsimp [t]; positivity
  have htHalf : t < 1 / 2 := by
    dsimp [t]
    linarith
  have hEu : 0 ≤ Eu := by
    dsimp [Eu]
    exact cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn R
      (publicCoeffField R (aCutoffFamily M L omega)) u.toH1.grad
      (publicCoeffField_isEllipticFieldOn_cubeSet R (aCutoffFamily M L omega))
  have hEw : 0 ≤ Ew := by
    dsimp [Ew]
    exact cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn R
      (publicCoeffField R (aCutoffFamily M L omega)) w.grad
      (publicCoeffField_isEllipticFieldOn_cubeSet R (aCutoffFamily M L omega))
  have hGsemi : 0 ≤ Gsemi := by
    dsimp [Gsemi, t]
    exact scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity hg
  have hBcirc : 0 ≤ Bcirc := by
    dsimp [Bcirc, Kcirc]
    exact mul_nonneg
      (mul_nonneg (cubeBesovScaleWeight_nonneg (-t) R)
        (mul_nonneg
          (inv_nonneg.mpr (geometricDiscount_pos (mul_pos ht (by norm_num))).le)
          (mul_nonneg (by positivity) (Real.sqrt_nonneg _))))
      (Real.sqrt_nonneg _)
  have hcirc : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm R t (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x ↦ w.grad x i) ≤ Bcirc := by
    intro i N
    have hraw := aCutoff_h1Gradient_descendant_circPartialNorm_le_of_parent_sixth_cap
      M L omega w hR hs (by exact le_rfl) hsigma hlower i N
    simpa only [W, t, Kcirc, Bcirc, Ew, mul_assoc] using! hraw
  have hweakRaw := weakFluxWithRHSRHS_descendant_le_of_parent_sixth_caps
    u hR hC.le hs hsigma hK hupper hlower hg (le_refl Gsemi)
  have hweak : weakFluxWithRHSRHS C R (aCutoffFamily M L omega) t
        (fun x ↦ -g₀ x) u +
      boundaryNegativeToL2Factor (2 * t) *
        boundaryNormalizedEuclideanL2 R (fun x ↦ -g₀ x) ≤
      Afac * Real.sqrt Eu + Gfac := by
    have henergy : forcedSolutionEnergyNorm R (aCutoffFamily M L omega) u =
        Real.sqrt Eu := by
      simpa only [Eu] using!
        forcedSolutionEnergyNorm_eq_sqrt_cubeAverage_coefficientEnergyDensity_publicCoeffField
          R (aCutoffFamily M L omega) u
    rw [henergy] at hweakRaw
    dsimp only [W, t, Afac, Gfac, Gsemi] at hweakRaw ⊢
    linarith only [hweakRaw]
  have hEwEq : cubeAverage R
      (coefficientEnergyDensity
        (publicCoeffField R (aCutoffFamily M L omega)) w.grad) = Ew := rfl
  have hEuEq : cubeAverage R
      (coefficientEnergyDensity
        (publicCoeffField R (aCutoffFamily M L omega)) u.toH1.grad) = Eu := rfl
  have hBcircEq : Bcirc = Kcirc * Real.sqrt Ew := rfl
  have hKcirc : 0 ≤ Kcirc := by
    dsimp [Kcirc]
    exact mul_nonneg (cubeBesovScaleWeight_nonneg (-t) R)
      (mul_nonneg
        (inv_nonneg.mpr (geometricDiscount_pos (mul_pos ht (by norm_num))).le)
        (mul_nonneg (by positivity) (Real.sqrt_nonneg _)))
  have hAfac : 0 ≤ Afac := by
    dsimp [Afac]
    exact mul_nonneg
      (mul_nonneg hC.le (inv_nonneg.mpr ht.le))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hGfac : 0 ≤ Gfac := by
    dsimp [Gfac]
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg hC.le (Real.rpow_nonneg ht.le _))
            (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) hGsemi)
      (mul_nonneg (boundaryNegativeToL2Factor_nonneg _)
        (boundaryNormalizedEuclideanL2_nonneg R _))
  have hresult := hquarter M L omega u w (eta := eta) (B := Bcut)
    (Bcirc := Bcirc) (Kcirc := Kcirc) (A := Afac) (G := Gfac)
    (Eu := Eu) (Eh := Eh) (Ew := Ew) height ht htHalf hg hBcut hBcirc
    hKcirc hAfac hGfac hEu hEh hxiLp hxi hderiv hcirc
    hBcircEq hEuEq hEwEq hsplit hweak hsmall
  simpa only [t, W, Eu, Ew, Gsemi, Kcirc, Bcirc, xi, Gs, Kfine, X₀, Xc,
    mu, rem, Afac, Gfac] using! hresult

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
