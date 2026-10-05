module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryArbitraryH1EnergyControl
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEllipticityCaps
public import Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.DescendantSummation.Gradient
public import Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicCanonicalGradient.Definitions

@[expose] public section

/-!
# Multiscale gradient control for arbitrary boundary data

The local harmonic-replacement energy control is fed into the existing
`q = 1` descendant summation.  This produces the coefficient-weighted
positive-side `circ` bounds used by the full-dual cutoff-product estimate,
without any pointwise lower ellipticity cap.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem memVectorL2_cubeSet_of_openCubeSet {Q : TriadicCube d}
    {F : Vec d → Vec d} (hF : MemVectorL2 (openCubeSet Q) F) :
    MemVectorL2 (cubeSet Q) F := by
  rw [MemVectorL2, volumeMeasureOn,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
  exact hF

/-- Full-dual Poincare is purely analytic and therefore applies to arbitrary
nonzero-boundary `H¹` data. -/
theorem boundaryH1_fullDualPoincare
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) (N : ℕ) :
    CubeDescendantDualFullVectorPoincareEstimate Q
      (fullVectorPoincareCubeConstant Q)
      (cubeFluctuation Q u.toFun) u.grad N := by
  simpa using CubeDescendantDualFullVectorPoincareEstimate.of_h1Function Q u N

/-- The `aCutoff` energy of arbitrary `H¹` data controls every finite `circ`
gradient norm through the multiscale `lambdaSq` factor. -/
theorem aCutoff_h1Gradient_circPartialNorm_le_energy
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    (r : ℝ) (hr : 0 < r) (i : Fin d) (N : ℕ) :
    cubeBesovCircPartialNorm Q r (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => u.grad x i) ≤
      (cubeBesovScaleWeight (-r) Q *
        ((geometricDiscount r 1)⁻¹ *
          Real.rpow
            (lambdaSq Q r (.finite 1)
              (publicCoeffField Q (aCutoffFamily M L omega)))
            (-1 / 2 : ℝ))) *
        Real.sqrt (cubeAverage Q
          (coefficientEnergyDensity
            (publicCoeffField Q (aCutoffFamily M L omega)) u.grad)) := by
  let A := aCutoffFamily M L omega
  let a := publicCoeffField Q A
  let energy := coefficientEnergyDensity a u.grad
  have hEll := publicCoeffField_isEllipticFieldOn_cubeSet Q A
  have henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x := by
    intro x hx
    exact coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEll u.grad x hx
  have henergy_int : IntegrableOn energy (cubeSet Q) :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll
      (memVectorL2_cubeSet_of_openCubeSet u.grad_memVectorL2)
  have hgrad : CubeAverageGradientEnergyControl Q a u.grad energy := by
    simpa only [A, a, energy] using
      aCutoff_cubeAverageGradientEnergyControl_of_h1Function M L omega Q u
  have hsum :=
    summable_qone_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
      Q a r hr hEll (publicCoeffField_openCubeDescendantDeterministicCoarseData Q A)
  simpa only [A, a, energy] using
    cubeBesovCircPartialNorm_component_le_local_canonicalGradientAcirc
      Q a r hr henergy_nonneg henergy_int hgrad hsum i N

/-- A single public lower-ellipticity cap at exponent `t` prices every
larger-exponent `circ` norm of an arbitrary `H¹` gradient.  This is the
coefficient-weighted replacement for the crude pointwise `lam⁻¹` estimate in
the nonzero-boundary cutoff leg. -/
theorem aCutoff_h1Gradient_circPartialNorm_le_of_lambdaSCap
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    {t r sigma K : ℝ} (ht : 0 < t) (htr : t ≤ r)
    (hcap : (Ch02.lambdaS Q t (aCutoffFamily M L omega))⁻¹ ≤ K * sigma⁻¹)
    (i : Fin d) (N : ℕ) :
    cubeBesovCircPartialNorm Q r (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => u.grad x i) ≤
      (cubeBesovScaleWeight (-r) Q *
        ((geometricDiscount r 1)⁻¹ *
          ((d : ℝ) * Real.sqrt (K * sigma⁻¹)))) *
        Real.sqrt (cubeAverage Q
          (coefficientEnergyDensity
            (publicCoeffField Q (aCutoffFamily M L omega)) u.grad)) := by
  let A := aCutoffFamily M L omega
  let a := publicCoeffField Q A
  let E := cubeAverage Q (coefficientEnergyDensity a u.grad)
  have hr : 0 < r := ht.trans_le htr
  have hraw := aCutoff_h1Gradient_circPartialNorm_le_energy
    M L omega Q u r hr i N
  have hmono : Ch02.lambdaSq Q t (.finite 1) A ≤
      Ch02.lambdaSq Q r (.finite 1) A := by
    rcases htr.eq_or_lt with hEq | hlt
    · rw [hEq]
    · exact Ch02.lambdaSq_finite_mono Q A ht hlt (by norm_num)
  have htpos : 0 < Ch02.lambdaSq Q t (.finite 1) A :=
    Ch02.lambdaSq_finite_pos Q A ht (by norm_num)
  have hinv : (Ch02.lambdaSq Q r (.finite 1) A)⁻¹ ≤
      (Ch02.lambdaSq Q t (.finite 1) A)⁻¹ := inv_anti₀ htpos hmono
  have hcap' : (Ch02.lambdaSq Q r (.finite 1) A)⁻¹ ≤ K * sigma⁻¹ := by
    exact hinv.trans (by simpa [Ch02.lambdaS] using hcap)
  have hsqrtPublic :
      Real.sqrt ((Ch02.lambdaSq Q r (.finite 1) A)⁻¹) ≤
        Real.sqrt (K * sigma⁻¹) :=
    Real.sqrt_le_sqrt hcap'
  have hbridge :=
    sqrt_lambdaSq_publicCoeffField_finite_one_inv_le_dim_mul_poincareLowerEllipticityFactor
      Q A hr
  have hpublicEq :
      poincareLowerEllipticityFactor Q A r (.finite 1) =
        Real.sqrt ((Ch02.lambdaSq Q r (.finite 1) A)⁻¹) := by
    unfold poincareLowerEllipticityFactor
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_eq_inv_rpow]
    rw [← Real.rpow_eq_pow]
  rw [hpublicEq] at hbridge
  have hfactor :
      Real.rpow (lambdaSq Q r (.finite 1) a) (-1 / 2 : ℝ) ≤
        (d : ℝ) * Real.sqrt (K * sigma⁻¹) := by
    have hdetEq :
        Real.rpow (lambdaSq Q r (.finite 1) a) (-1 / 2 : ℝ) =
          Real.sqrt ((lambdaSq Q r (.finite 1) a)⁻¹) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_eq_inv_rpow]
      rw [← Real.rpow_eq_pow]
      ring_nf
    rw [hdetEq]
    exact hbridge.trans
      (mul_le_mul_of_nonneg_left hsqrtPublic (by positivity))
  have hdisc : 0 ≤ (geometricDiscount r 1)⁻¹ :=
    inv_nonneg.mpr (geometricDiscount_pos (by simpa using hr)).le
  have hscale : 0 ≤ cubeBesovScaleWeight (-r) Q :=
    cubeBesovScaleWeight_nonneg (-r) Q
  have hsqrtE : 0 ≤ Real.sqrt E := Real.sqrt_nonneg _
  have hscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hfactor hdisc) hscale) hsqrtE
  simpa only [A, a, E, mul_assoc] using hraw.trans hscaled

/-- On the manuscript good event, the nonzero-boundary scalar factor has the
two (and indeed all) larger-exponent `circ` controls needed by the full-dual
cutoff-product estimate.  The only coefficient price is
`sqrt (B * sigma⁻¹)`, where `B` is dimension-only. -/
theorem exists_localBoundaryH1CircCaps (d : ℕ) [NeZero d] :
    ∃ B : ℝ, 0 < B ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L m n : ℕ, m ≤ L → n + 5 ≤ m → ∀ z x y omega,
        x ∈ truncatedCube d m (n - 3) z →
        translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x →
        omega ∈ goodEvent M none (n + 2) z 1 (s / 8) →
        let Q := originCube d ((n : ℤ) - 2)
        let A := aCutoffFamily M L (translatePotentialSample y omega)
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        ∀ (u : H1Function (openCubeSet Q)) (r : ℝ), s / 3 ≤ r →
          ∀ i : Fin d, ∀ N : ℕ,
          cubeBesovCircPartialNorm Q r (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
              (fun q => u.grad q i) ≤
            (cubeBesovScaleWeight (-r) Q *
              ((geometricDiscount r 1)⁻¹ *
                ((d : ℝ) * Real.sqrt (B * sigma⁻¹)))) *
              Real.sqrt (cubeAverage Q
                (coefficientEnergyDensity (publicCoeffField Q A) u.grad)) := by
  obtain ⟨E₀, B, hE₀, hB, hcaps⟩ := exists_localBoundaryEllipticityCaps d
  refine ⟨B, hB, ?_⟩
  intro M s hs L m n hmL hnm z x y omega hx hD hgood
  dsimp only
  let Q := originCube d ((n : ℤ) - 2)
  let A := aCutoffFamily M L (translatePotentialSample y omega)
  let sigma := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  have hnL : n + 2 ≤ L := by omega
  have hlocal := hcaps M s hs L m n hnL z x y omega hx hD hgood
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  intro u r hsr i N
  have hraw := aCutoff_h1Gradient_circPartialNorm_le_of_lambdaSCap
    M L (translatePotentialSample y omega) Q u
      (t := s / 3) (r := r) (sigma := sigma) (K := B)
      (div_pos hs0 (by norm_num)) hsr hlocal.2.2.2.2.1 i N
  simpa only [Q, A, sigma] using hraw

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
