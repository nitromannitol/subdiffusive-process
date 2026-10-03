module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryWeightedFiniteHeightProduct
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryGoodEventAbsorption

@[expose] public section

/-!
# Good-event weighted cutoff absorption

This file composes the finite-height nonzero-datum cutoff product with the
manuscript good event.  The resulting fine coefficient contains
`sqrt sigma⁻¹`, while the solution part of the weak flux contains
`sqrt sigma`; the two cancel in the height-choice obligation.  No pointwise
upper or lower coefficient cap is used.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- Young absorption when the cutoff product is measured by the energy of a
difference `w`, and that energy splits into solution and datum energies. -/
theorem halfAbsorb_of_twoEnergy_product_budget
    {pair C A Eu Eh Ew G mu R : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hEu : 0 ≤ Eu) (hEh : 0 ≤ Eh)
    (hG : 0 ≤ G) (hmu : 0 ≤ mu)
    (hpair : |pair| ≤ C * (A * Real.sqrt Eu + G) *
      (mu * Real.sqrt Ew + R))
    (hsplit : Ew ≤ 2 * Eu + 2 * Eh)
    (hsmall : C * A * (Real.sqrt 2 * mu) ≤ 1 / 8) :
    let R' := Real.sqrt 2 * mu * Real.sqrt Eh + R
    |pair| ≤
      (1 / 4 : ℝ) * Eu +
        4 * (C * A * R') ^ 2 +
        4 * (C * G * (Real.sqrt 2 * mu)) ^ 2 + C * G * R' := by
  dsimp only
  have hsum : 0 ≤ 2 * Eu + 2 * Eh := by positivity
  have hsqrt : Real.sqrt Ew ≤
      Real.sqrt 2 * Real.sqrt Eu + Real.sqrt 2 * Real.sqrt Eh := by
    calc
      Real.sqrt Ew ≤ Real.sqrt (2 * Eu + 2 * Eh) := Real.sqrt_le_sqrt hsplit
      _ ≤ Real.sqrt (2 * Eu) + Real.sqrt (2 * Eh) :=
        sqrt_add_le_add_sqrt_of_nonneg (by positivity) (by positivity)
      _ = Real.sqrt 2 * Real.sqrt Eu + Real.sqrt 2 * Real.sqrt Eh := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hbudget : mu * Real.sqrt Ew + R ≤
      (Real.sqrt 2 * mu) * Real.sqrt Eu +
        (Real.sqrt 2 * mu * Real.sqrt Eh + R) := by
    have hscaled := mul_le_mul_of_nonneg_left hsqrt hmu
    nlinarith only [hscaled]
  exact halfAbsorb_of_product_budget hC hA hEu hG hpair hbudget hsmall

omit [NeZero d] in
/-- The sharper version used when one product carries the sum of the
residual and twice the affine-lift flux.  The common height is chosen with
twice the usual prefactor, so the fine term spends only one eighth of the
combined solution energy. -/
theorem eighthAbsorb_of_twoEnergy_product_budget
    {pair C A Eu Eh Ew G mu R : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hEu : 0 ≤ Eu) (hEh : 0 ≤ Eh)
    (hG : 0 ≤ G) (hmu : 0 ≤ mu)
    (hpair : |pair| ≤ C * (A * Real.sqrt Eu + G) *
      (mu * Real.sqrt Ew + R))
    (hsplit : Ew ≤ 2 * Eu + 2 * Eh)
    (hsmall : C * A * (Real.sqrt 2 * mu) ≤ 1 / 16) :
    let R' := Real.sqrt 2 * mu * Real.sqrt Eh + R
    |pair| ≤
      (1 / 8 : ℝ) * Eu +
        8 * (C * A * R') ^ 2 +
        8 * (C * G * (Real.sqrt 2 * mu)) ^ 2 + C * G * R' := by
  dsimp only
  have hsum : 0 ≤ 2 * Eu + 2 * Eh := by positivity
  have hsqrt : Real.sqrt Ew ≤
      Real.sqrt 2 * Real.sqrt Eu + Real.sqrt 2 * Real.sqrt Eh := by
    calc
      Real.sqrt Ew ≤ Real.sqrt (2 * Eu + 2 * Eh) := Real.sqrt_le_sqrt hsplit
      _ ≤ Real.sqrt (2 * Eu) + Real.sqrt (2 * Eh) :=
        sqrt_add_le_add_sqrt_of_nonneg (by positivity) (by positivity)
      _ = Real.sqrt 2 * Real.sqrt Eu + Real.sqrt 2 * Real.sqrt Eh := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hbudget : mu * Real.sqrt Ew + R ≤
      (Real.sqrt 2 * mu) * Real.sqrt Eu +
        (Real.sqrt 2 * mu * Real.sqrt Eh + R) := by
    have hscaled := mul_le_mul_of_nonneg_left hsqrt hmu
    nlinarith only [hscaled]
  let mu' := Real.sqrt 2 * mu
  let R' := Real.sqrt 2 * mu * Real.sqrt Eh + R
  have hpair' : |pair| ≤ C * (A * Real.sqrt Eu + G) *
      (mu' * Real.sqrt Eu + R') := by
    exact hpair.trans (mul_le_mul_of_nonneg_left hbudget
      (mul_nonneg hC (add_nonneg
        (mul_nonneg hA (Real.sqrt_nonneg _)) hG)))
  have hsmallE : C * A * mu' * Eu ≤ (1 / 16 : ℝ) * Eu :=
    mul_le_mul_of_nonneg_right hsmall hEu
  have hcrossA : C * A * R' * Real.sqrt Eu ≤
      (1 / 32 : ℝ) * Eu + 8 * (C * A * R') ^ 2 := by
    have hsqrtSq : (Real.sqrt Eu) ^ 2 = Eu := Real.sq_sqrt hEu
    let y := C * A * R'
    have hyoung : Real.sqrt Eu * y ≤
        (1 / 32 : ℝ) * (Real.sqrt Eu) ^ 2 + 8 * y ^ 2 := by
      nlinarith only [sq_nonneg (Real.sqrt Eu - 16 * y)]
    dsimp only [y] at hyoung
    rw [hsqrtSq] at hyoung
    nlinarith only [hyoung]
  have hcrossG : C * G * mu' * Real.sqrt Eu ≤
      (1 / 32 : ℝ) * Eu + 8 * (C * G * mu') ^ 2 := by
    have hsqrtSq : (Real.sqrt Eu) ^ 2 = Eu := Real.sq_sqrt hEu
    let y := C * G * mu'
    have hyoung : Real.sqrt Eu * y ≤
        (1 / 32 : ℝ) * (Real.sqrt Eu) ^ 2 + 8 * y ^ 2 := by
      nlinarith only [sq_nonneg (Real.sqrt Eu - 16 * y)]
    dsimp only [y] at hyoung
    rw [hsqrtSq] at hyoung
    nlinarith only [hyoung]
  have hexpand : C * (A * Real.sqrt Eu + G) *
      (mu' * Real.sqrt Eu + R') =
      C * A * mu' * Eu + C * A * R' * Real.sqrt Eu +
        C * G * mu' * Real.sqrt Eu + C * G * R' := by
    calc
      C * (A * Real.sqrt Eu + G) * (mu' * Real.sqrt Eu + R') =
          C * A * mu' * (Real.sqrt Eu) ^ 2 +
            C * A * R' * Real.sqrt Eu +
            C * G * mu' * Real.sqrt Eu + C * G * R' := by ring
      _ = _ := by rw [Real.sq_sqrt hEu]
  rw [hexpand] at hpair'
  dsimp only [mu', R'] at hpair' hsmallE hcrossA hcrossG ⊢
  linarith only [hpair', hsmallE, hcrossA, hcrossG]

omit [NeZero d] in
/-- Joint absorption for the signed affine/residual product.  The flux
energy is that of `r + 2 v`, whereas the value factor is `r - h`; keeping the
two energy decompositions separate is what prevents an invalid cancellation
argument. -/
theorem quarterResidualAbsorb_of_combinedFlux_product_budget
    {pair C A Ecomb Er Ev Eh Ew G mu R : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hEcomb : 0 ≤ Ecomb) (hEw : 0 ≤ Ew) (hmu : 0 ≤ mu)
    (hpair : |pair| ≤ C * (A * Real.sqrt Ecomb + G) *
      (mu * Real.sqrt Ew + R))
    (hcomb : Ecomb ≤ 2 * Er + 8 * Ev)
    (hvalue : Ew ≤ 2 * Er + 2 * Eh)
    (hsmall : C * A * (Real.sqrt 2 * mu) ≤ 1 / 8) :
    |pair| ≤
      (1 / 4 : ℝ) * Er + (1 / 2 : ℝ) * Ev +
        (1 / 8 : ℝ) * Eh +
        16 * (C * A * R) ^ 2 + 16 * (C * G * mu) ^ 2 + C * G * R := by
  have hsqrt2 : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hmuSmall : C * A * mu ≤ 3 / 32 := by
    have hscaled : (4 / 3 : ℝ) * (C * A * mu) ≤
        Real.sqrt 2 * (C * A * mu) :=
      mul_le_mul_of_nonneg_right hsqrt2
        (mul_nonneg (mul_nonneg hC hA) hmu)
    have hrewrite : Real.sqrt 2 * (C * A * mu) =
        C * A * (Real.sqrt 2 * mu) := by ring
    rw [hrewrite] at hscaled
    nlinarith only [hscaled, hsmall]
  have hmain : C * A * mu * Real.sqrt Ecomb * Real.sqrt Ew ≤
      (3 / 16 : ℝ) * Er + (3 / 8 : ℝ) * Ev + (3 / 32 : ℝ) * Eh := by
    have hsqrtProd : Real.sqrt Ecomb * Real.sqrt Ew ≤ (Ecomb + Ew) / 2 := by
      have hsq := sq_nonneg (Real.sqrt Ecomb - Real.sqrt Ew)
      nlinarith only [hsq, Real.sq_sqrt hEcomb, Real.sq_sqrt hEw]
    have hfront : 0 ≤ C * A * mu := mul_nonneg (mul_nonneg hC hA) hmu
    have hscaled := mul_le_mul_of_nonneg_left hsqrtProd hfront
    have hsum : Ecomb + Ew ≤ 4 * Er + 8 * Ev + 2 * Eh := by
      linarith only [hcomb, hvalue]
    have hscaledSmall := mul_le_mul_of_nonneg_right hmuSmall
      (by positivity : 0 ≤ (Ecomb + Ew) / 2)
    nlinarith only [hscaled, hsum, hscaledSmall]
  have hcrossA : C * A * R * Real.sqrt Ecomb ≤
      (1 / 32 : ℝ) * Er + (1 / 8 : ℝ) * Ev +
        16 * (C * A * R) ^ 2 := by
    let y := C * A * R
    have hyoung : Real.sqrt Ecomb * y ≤
        (1 / 64 : ℝ) * Ecomb + 16 * y ^ 2 := by
      have hs := sq_nonneg (Real.sqrt Ecomb - 32 * y)
      nlinarith only [hs, Real.sq_sqrt hEcomb]
    dsimp only [y] at hyoung
    nlinarith only [hyoung, hcomb]
  have hcrossG : C * G * mu * Real.sqrt Ew ≤
      (1 / 32 : ℝ) * Er + (1 / 32 : ℝ) * Eh +
        16 * (C * G * mu) ^ 2 := by
    let y := C * G * mu
    have hyoung : Real.sqrt Ew * y ≤
        (1 / 64 : ℝ) * Ew + 16 * y ^ 2 := by
      have hs := sq_nonneg (Real.sqrt Ew - 32 * y)
      nlinarith only [hs, Real.sq_sqrt hEw]
    dsimp only [y] at hyoung
    nlinarith only [hyoung, hvalue]
  have hexpand : C * (A * Real.sqrt Ecomb + G) *
      (mu * Real.sqrt Ew + R) =
      C * A * mu * Real.sqrt Ecomb * Real.sqrt Ew +
        C * A * R * Real.sqrt Ecomb +
        C * G * mu * Real.sqrt Ew + C * G * R := by ring
  rw [hexpand] at hpair
  linarith only [hpair, hmain, hcrossA, hcrossG]

omit [NeZero d] in
/-- The coefficient energy of the nonzero boundary difference has the
universal two-plus-two split. -/
theorem cubeAverage_coefficientEnergyDensity_h1Sub_le_two_mul_add
    (Q : TriadicCube d) (a : CoeffFamily d)
    (u h : H1Function (openCubeSet Q)) :
    cubeAverage Q
        (coefficientEnergyDensity (publicCoeffField Q a) (u - h).grad) ≤
      2 * cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a) u.grad) +
        2 * cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a) h.grad) := by
  have hcube : volume.restrict (cubeSet Q) = volume.restrict (openCubeSet Q) :=
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q
  have hu : MemVectorL2 (cubeSet Q) u.grad := by
    rw [MemVectorL2, volumeMeasureOn, hcube]
    exact u.grad_memVectorL2
  have hh : MemVectorL2 (cubeSet Q) h.grad := by
    rw [MemVectorL2, volumeMeasureOn, hcube]
    exact h.grad_memVectorL2
  have hw : MemVectorL2 (cubeSet Q) (u - h).grad := by
    rw [MemVectorL2, volumeMeasureOn, hcube]
    exact (u - h).grad_memVectorL2
  let H : Vec d → Vec d := fun x => -h.grad x
  have hH : MemVectorL2 (cubeSet Q) H := by
    simpa only [H] using! hh.neg
  have hsum : (u - h).grad =ᵐ[volume.restrict (cubeSet Q)]
      fun x => u.grad x + H x := by
    filter_upwards with x
    rw [H1Function.sub_grad]
    rfl
  have hraw := cubeAverage_coefficientEnergyDensity_le_two_mul_add_of_ae_eq_add
    (publicCoeffField_isEllipticFieldOn_cubeSet Q a) hw hu hH hsum
  have hneg : cubeAverage Q
      (coefficientEnergyDensity (publicCoeffField Q a) H) =
      cubeAverage Q
        (coefficientEnergyDensity (publicCoeffField Q a) h.grad) := by
    congr 1
    funext x
    simp [H, coefficientEnergyDensity, matVecMul_neg, vecDot_neg_left,
      vecDot_neg_right]
  rw [hneg] at hraw
  exact hraw

/-- Good-event cutoff pairing with its absorbable fine coefficient `mu` and
coarse `L²` remainder `R` exposed. -/
theorem exists_localBoundaryWeightedCutoffPairingBudget (d : ℕ) [NeZero d] :
    ∃ Cp Cw Bc Bw : ℝ,
      0 < Cp ∧ 0 < Cw ∧ 0 < Bc ∧ 0 < Bw ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L m n : ℕ, m ≤ L → n + 5 ≤ m → ∀ z x y omega,
        x ∈ truncatedCube d m (n - 3) z →
        translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x →
        omega ∈ goodEvent M none (n + 2) z 1 (s / 8) →
        let Q := originCube d ((n : ℤ) - 2)
        let A := aCutoffFamily M L (translatePotentialSample y omega)
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        ∀ (g : Vec d → Vec d) (u : ForcedCubeSolution Q A g)
          (w : H1Function (openCubeSet Q))
          (eta : Vec d → ℝ) (Bcut : ℝ) (height : ℕ),
          ForceBesovRegularity Q (s / 3) g →
          ContDiff ℝ (⊤ : ℕ∞) eta → HasCompactSupport eta →
          tsupport eta ⊆ openCubeSet Q → 0 ≤ Bcut →
          MemLp (scalarCutoffGradientField eta) ∞ (normalizedCubeMeasure Q) →
          (∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞)
            (fun q => scalarCutoffGradientField eta q i)) →
          (∀ i : Fin d, ∀ q ∈ cubeSet Q,
            ‖fderiv ℝ (fun p => scalarCutoffGradientField eta p i) q‖ ≤ Bcut) →
          Integrable (fun q =>
            vecDot (forcedSolutionCorrectedFluxField Q A g u q)
              (w.toFun q • scalarCutoffGradientField eta q))
            (normalizedCubeMeasure Q) →
          Integrable (fun q =>
            vecDot (forcedSolutionCorrectedFluxField Q A g u q)
              ((cubeAverage Q w.toFun) • scalarCutoffGradientField eta q))
            (normalizedCubeMeasure Q) →
          let t := s / 3
          let xi := scalarCutoffGradientField eta
          let Ew := cubeAverage Q
            (coefficientEnergyDensity (publicCoeffField Q A) w.grad)
          let Eu := cubeAverage Q
            (coefficientEnergyDensity (publicCoeffField Q A) u.toH1.grad)
          let X := cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q w.toFun)
          let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
          let Kcirc := cubeBesovScaleWeight (-t) Q *
            ((geometricDiscount t 1)⁻¹ * ((d : ℝ) * Real.sqrt (Bc * sigma⁻¹)))
          let Kfine := cubeBesovScaleWeight (-(1 - t)) Q *
            ((fullVectorPoincareCubeConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Kcirc))
          let mu := 2 * cubeLpNorm Q ∞ xi *
            boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height * Kfine
          let R := (d : ℝ) * cubeLpNorm Q ∞ xi * X +
            2 * (cubeScaleFactor Q * Bcut * (Gs * X) +
              cubeLpNorm Q ∞ xi *
                (boundaryFiniteHeightHeadGlobalCoeff t height * X))
          let Afac := Cp * t⁻¹ * (Real.sqrt Bw * Real.sqrt sigma)
          let Gfac :=
            Cp * Real.rpow t (-(5 / 2 : ℝ)) *
                (Real.sqrt Bw * Real.sqrt sigma) *
                (Real.sqrt Bw * Real.sqrt sigma⁻¹) *
                scaleNormalizedPositiveBesovVectorSeminormTwo Q t g +
              boundaryNegativeToL2Factor (2 * t) *
                boundaryNormalizedEuclideanL2 Q g
          |cubeAverage Q (fun q =>
            vecDot (forcedSolutionCorrectedFluxField Q A g u q)
              (w.toFun q • xi q))| ≤
            Cp * (Afac * Real.sqrt Eu + Gfac) *
              (mu * Real.sqrt Ew + R) := by
  obtain ⟨Cp, hCp, hpair⟩ :=
    exists_abs_correctedFlux_h1CutoffPairing_weightedFiniteHeight_le d
  obtain ⟨Cw, hCw, hweak⟩ := exists_localBoundaryWeakFluxCap d
  obtain ⟨Bc, hBc, hcirc⟩ := exists_localBoundaryH1CircCaps d
  let Bw := max Bc Cw
  have hBw : 0 < Bw := hBc.trans_le (le_max_left Bc Cw)
  refine ⟨Cp, Cw, Bc, Bw, hCp, hCw, hBc, hBw, ?_⟩
  intro M s hs L m n hmL hnm z x y omega hx hD hgood
  dsimp only
  let Q := originCube d ((n : ℤ) - 2)
  let A := aCutoffFamily M L (translatePotentialSample y omega)
  let sigma := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  intro g u w eta Bcut height hg heta hetaCompact hetaSupport hBcut
    hxiLp hxi hderiv hmain hconst
  let t := s / 3
  let xi := scalarCutoffGradientField eta
  let Ew := cubeAverage Q
    (coefficientEnergyDensity (publicCoeffField Q A) w.grad)
  let Eu := cubeAverage Q
    (coefficientEnergyDensity (publicCoeffField Q A) u.toH1.grad)
  let X := cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q w.toFun)
  let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
  let Kcirc := cubeBesovScaleWeight (-t) Q *
    ((geometricDiscount t 1)⁻¹ * ((d : ℝ) * Real.sqrt (Bc * sigma⁻¹)))
  let Bcirc := Kcirc * Real.sqrt Ew
  let Kfine := cubeBesovScaleWeight (-(1 - t)) Q *
    ((fullVectorPoincareCubeConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ((Fintype.card (Fin d) : ℝ) * Kcirc))
  let mu := 2 * cubeLpNorm Q ∞ xi *
    boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height * Kfine
  let R := (d : ℝ) * cubeLpNorm Q ∞ xi * X +
    2 * (cubeScaleFactor Q * Bcut * (Gs * X) +
      cubeLpNorm Q ∞ xi * (boundaryFiniteHeightHeadGlobalCoeff t height * X))
  let Afac := Cp * t⁻¹ * (Real.sqrt Bw * Real.sqrt sigma)
  let Gfac := Cp * Real.rpow t (-(5 / 2 : ℝ)) *
      (Real.sqrt Bw * Real.sqrt sigma) *
      (Real.sqrt Bw * Real.sqrt sigma⁻¹) *
      scaleNormalizedPositiveBesovVectorSeminormTwo Q t g +
    boundaryNegativeToL2Factor (2 * t) * boundaryNormalizedEuclideanL2 Q g
  have ht : 0 < t := by
    dsimp [t]
    exact div_pos
      ((mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1)
      (by norm_num)
  have htHalf : t < 1 / 2 := by dsimp [t]; linarith only [hs.2]
  have hBcirc : 0 ≤ Bcirc := by
    dsimp [Bcirc, Kcirc]
    exact mul_nonneg
      (mul_nonneg (cubeBesovScaleWeight_nonneg (-t) Q)
        (mul_nonneg (inv_nonneg.mpr (geometricDiscount_pos (mul_pos ht (by norm_num))).le)
          (mul_nonneg (by positivity) (Real.sqrt_nonneg _))))
      (Real.sqrt_nonneg _)
  have hcirc' : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q t (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun q => w.grad q i) ≤ Bcirc := by
    intro i N
    have hraw := hcirc M s hs L m n hmL hnm z x y omega hx hD hgood
      w t (le_refl _) i N
    simpa only [Q, A, sigma, t, Ew, Kcirc, Bcirc, mul_assoc] using! hraw
  have hp := hpair (Q := Q) (a := A) (t := t) (g := g) u w
    (eta := eta) (B := Bcut) (Bcirc := Bcirc) height ht htHalf
    (by simpa only [t] using! hg) heta hetaCompact hetaSupport hBcut hBcirc
    hxiLp hxi hderiv hcirc' hmain hconst
  dsimp only at hp
  have hweak' := hweak M s hs L m n hmL hnm z x y omega hx hD hgood
    Cp (scaleNormalizedPositiveBesovVectorSeminormTwo Q t g) g u hCp.le
      (by simpa only [t] using! hg) le_rfl
  have hBwBc : Cw ≤ Bw := le_max_right _ _
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2) (translatePotentialSample z omega)
  have hsqrtB : Real.sqrt Cw ≤ Real.sqrt Bw := Real.sqrt_le_sqrt hBwBc
  have hA : Cp * t⁻¹ * (Real.sqrt Cw * Real.sqrt sigma) ≤ Afac := by
    dsimp [Afac]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hsqrtB (Real.sqrt_nonneg _))
      (mul_nonneg hCp.le (inv_nonneg.mpr ht.le))
  have hGfac :
      Cp * Real.rpow t (-(5 / 2 : ℝ)) *
          (Real.sqrt Cw * Real.sqrt sigma) *
          (Real.sqrt Cw * Real.sqrt sigma⁻¹) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q t g +
        boundaryNegativeToL2Factor (2 * t) * boundaryNormalizedEuclideanL2 Q g ≤
      Gfac := by
    dsimp [Gfac]
    have hrootSigma : 0 ≤ Real.sqrt sigma := Real.sqrt_nonneg _
    have hrootInv : 0 ≤ Real.sqrt sigma⁻¹ := Real.sqrt_nonneg _
    have hsemi : 0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo Q t g :=
      scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
        (by simpa only [t] using! hg)
    gcongr
  have hEu : forcedSolutionEnergyNorm Q A u = Real.sqrt Eu := by
    simpa only [Eu] using!
      forcedSolutionEnergyNorm_eq_sqrt_cubeAverage_coefficientEnergyDensity_publicCoeffField
        Q A u
  rw [hEu] at hweak'
  have hweak'' : weakFluxWithRHSRHS Cp Q A t g u ≤
      Cp * t⁻¹ * (Real.sqrt Cw * Real.sqrt sigma) * Real.sqrt Eu +
        Cp * Real.rpow t (-(5 / 2 : ℝ)) *
          (Real.sqrt Cw * Real.sqrt sigma) *
          (Real.sqrt Cw * Real.sqrt sigma⁻¹) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q t g := by
    simpa only [Q, A, t, sigma] using! hweak'
  have hweakSum : weakFluxWithRHSRHS Cp Q A t g u +
        boundaryNegativeToL2Factor (2 * t) * boundaryNormalizedEuclideanL2 Q g ≤
      Afac * Real.sqrt Eu + Gfac := by
    calc
      _ ≤ (Cp * t⁻¹ * (Real.sqrt Cw * Real.sqrt sigma) * Real.sqrt Eu +
            Cp * Real.rpow t (-(5 / 2 : ℝ)) *
              (Real.sqrt Cw * Real.sqrt sigma) *
              (Real.sqrt Cw * Real.sqrt sigma⁻¹) *
              scaleNormalizedPositiveBesovVectorSeminormTwo Q t g) +
            boundaryNegativeToL2Factor (2 * t) *
              boundaryNormalizedEuclideanL2 Q g := add_le_add hweak'' le_rfl
      _ = Cp * t⁻¹ * (Real.sqrt Cw * Real.sqrt sigma) * Real.sqrt Eu +
          (Cp * Real.rpow t (-(5 / 2 : ℝ)) *
              (Real.sqrt Cw * Real.sqrt sigma) *
              (Real.sqrt Cw * Real.sqrt sigma⁻¹) *
              scaleNormalizedPositiveBesovVectorSeminormTwo Q t g +
            boundaryNegativeToL2Factor (2 * t) *
              boundaryNormalizedEuclideanL2 Q g) := by ring
      _ ≤ Afac * Real.sqrt Eu + Gfac := add_le_add
        (mul_le_mul_of_nonneg_right hA (Real.sqrt_nonneg _)) hGfac
  have hP :
      (d : ℝ) * cubeLpNorm Q ∞ xi * X +
          2 * (cubeScaleFactor Q * Bcut * (Gs * X) +
            cubeLpNorm Q ∞ xi *
              (boundaryFiniteHeightHeadGlobalCoeff t height * X +
                boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height *
                  (cubeBesovScaleWeight (-(1 - t)) Q *
                    ((fullVectorPoincareCubeConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
                      ((Fintype.card (Fin d) : ℝ) * Bcirc))))) =
        mu * Real.sqrt Ew + R := by
    dsimp [mu, R, Kfine, Bcirc]
    ring
  rw [hP] at hp
  have hPnonneg : 0 ≤ mu * Real.sqrt Ew + R := by
    rw [← hP]
    have hX : 0 ≤ X := by dsimp [X]; exact cubeLpNorm_nonneg Q 2 _
    have hxiNorm : 0 ≤ cubeLpNorm Q ∞ xi := cubeLpNorm_nonneg Q ∞ xi
    have hhead : 0 ≤ boundaryFiniteHeightHeadGlobalCoeff t height :=
      boundaryFiniteHeightHeadGlobalCoeff_nonneg t height
    have htail : 0 ≤ boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height :=
      boundaryFiniteHeightTailBetweenGlobalCoeff_nonneg t (1 - t) height
    have hBr : 0 ≤ cubeBesovScaleWeight (-(1 - t)) Q *
        ((fullVectorPoincareCubeConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((Fintype.card (Fin d) : ℝ) * Bcirc)) :=
      mul_nonneg (cubeBesovScaleWeight_nonneg (-(1 - t)) Q)
        (mul_nonneg
          (mul_nonneg (fullVectorPoincareCubeConstant_nonneg Q)
            (Real.rpow_nonneg (by norm_num) _))
          (mul_nonneg (by positivity) hBcirc))
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by positivity) hxiNorm) hX)
      (mul_nonneg (by norm_num)
        (add_nonneg
          (mul_nonneg (mul_nonneg (cubeScaleFactor_nonneg Q) hBcut)
            (mul_nonneg (Real.sqrt_nonneg _) hX))
          (mul_nonneg hxiNorm
            (add_nonneg (mul_nonneg hhead hX) (mul_nonneg htail hBr)))))
  have hscaled : Cp *
        (weakFluxWithRHSRHS Cp Q A t g u +
          boundaryNegativeToL2Factor (2 * t) * boundaryNormalizedEuclideanL2 Q g) *
        (mu * Real.sqrt Ew + R) ≤
      Cp * (Afac * Real.sqrt Eu + Gfac) * (mu * Real.sqrt Ew + R) := by
    simpa only [mul_assoc] using! mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hweakSum hPnonneg) hCp.le
  have hfinal := hp.trans hscaled
  simpa only [Q, A, sigma, t, xi, Ew, Eu, X, Gs, Kcirc, Kfine, mu, R,
    Afac, Gfac] using! hfinal

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
