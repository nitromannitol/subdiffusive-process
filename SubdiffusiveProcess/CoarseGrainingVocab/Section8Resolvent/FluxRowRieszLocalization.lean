import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowLocalLocalization
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszMassive




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Homogenization
open SubdiffusiveProcess.Frozen.Section8
open scoped BigOperators

noncomputable section

variable {ι : Type*}

/-- Applying deterministic localization to the real and imaginary parts of a
complex pairing gives the corresponding squared complex-norm estimate. -/
theorem complex_fluxRowDeterministicLocalization
    (cells : Finset ι) (volume localNegative localTest : ι → ℝ)
    (pairingRe pairingIm : ι → ℝ) (globalTest K : ℝ)
    (hvolume : ∀ a ∈ cells, 0 ≤ volume a)
    (hnegative : ∀ a ∈ cells, 0 ≤ localNegative a)
    (htest : ∀ a ∈ cells, 0 ≤ localTest a)
    (hpairRe : ∀ a ∈ cells,
      |pairingRe a| ≤ localNegative a * localTest a)
    (hpairIm : ∀ a ∈ cells,
      |pairingIm a| ≤ localNegative a * localTest a)
    (hpositive : fluxRowLocalTestSumSq cells volume localTest ≤
      K * globalTest ^ 2)
    (z : ℂ)
    (hzRe : z.re = fluxRowLocalizedPairing cells volume pairingRe)
    (hzIm : z.im = fluxRowLocalizedPairing cells volume pairingIm) :
    ‖z‖ ^ 2 ≤
      2 * K * fluxRowLocalNegativeSumSq cells volume localNegative *
        globalTest ^ 2 := by
  have hre := fluxRowDeterministicLocalization cells volume localNegative
    localTest pairingRe globalTest K hvolume hnegative htest hpairRe hpositive
  have him := fluxRowDeterministicLocalization cells volume localNegative
    localTest pairingIm globalTest K hvolume hnegative htest hpairIm hpositive
  rw [Complex.sq_norm, Complex.normSq_apply, ← sq, ← sq, hzRe, hzIm]
  nlinarith

/-- Norm form of the complex finite-cell localization estimate. -/
theorem norm_complex_fluxRowDeterministicLocalization_le
    (cells : Finset ι) (volume localNegative localTest : ι → ℝ)
    (pairingRe pairingIm : ι → ℝ) (globalTest K : ℝ)
    (hK : 0 ≤ K) (hglobalTest : 0 ≤ globalTest)
    (hvolume : ∀ a ∈ cells, 0 ≤ volume a)
    (hnegative : ∀ a ∈ cells, 0 ≤ localNegative a)
    (htest : ∀ a ∈ cells, 0 ≤ localTest a)
    (hpairRe : ∀ a ∈ cells,
      |pairingRe a| ≤ localNegative a * localTest a)
    (hpairIm : ∀ a ∈ cells,
      |pairingIm a| ≤ localNegative a * localTest a)
    (hpositive : fluxRowLocalTestSumSq cells volume localTest ≤
      K * globalTest ^ 2)
    (z : ℂ)
    (hzRe : z.re = fluxRowLocalizedPairing cells volume pairingRe)
    (hzIm : z.im = fluxRowLocalizedPairing cells volume pairingIm) :
    ‖z‖ ≤
      Real.sqrt
          (2 * K * fluxRowLocalNegativeSumSq cells volume localNegative) *
        globalTest := by
  have hnegativeSum :
      0 ≤ fluxRowLocalNegativeSumSq cells volume localNegative := by
    unfold fluxRowLocalNegativeSumSq
    apply Finset.sum_nonneg
    intro a ha
    exact mul_nonneg (hvolume a ha) (sq_nonneg _)
  have hcoefficient :
      0 ≤ 2 * K * fluxRowLocalNegativeSumSq cells volume localNegative :=
    mul_nonneg (mul_nonneg (by norm_num) hK) hnegativeSum
  have hsquare := complex_fluxRowDeterministicLocalization cells volume
    localNegative localTest pairingRe pairingIm globalTest K hvolume hnegative
    htest hpairRe hpairIm hpositive z hzRe hzIm
  apply (sq_le_sq₀ (norm_nonneg z)
    (mul_nonneg (Real.sqrt_nonneg _) hglobalTest)).mp
  calc
    ‖z‖ ^ 2 ≤
        2 * K * fluxRowLocalNegativeSumSq cells volume localNegative *
          globalTest ^ 2 := hsquare
    _ = (Real.sqrt
          (2 * K * fluxRowLocalNegativeSumSq cells volume localNegative) *
        globalTest) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hcoefficient]

/-- A finite stopping-cell family, with separate real and imaginary local
pairing estimates, supplies the global Schwartz bound required by the
weighted Riesz construction.  This is the exact finite-family composition;
an infinite stopping partition must first be exhausted by such families. -/
theorem exists_fluxHat_massiveNegativeSobolevNormSq_le_of_finite_localization
    {d : ℕ} {R sigma : ℝ} (hR : 0 < R) (F : Vec d → Vec d)
    (htestMem : ∀ phi : SchwartzMap (Vec d) ℂ,
      MemLp (phi : Vec d → ℂ) 2
        (volume.withDensity fun xi ↦ fluxRowMassiveTestDensity R sigma xi))
    (L : Fin d → SchwartzMap (Vec d) ℂ →ₗ[ℂ] ℂ)
    (hphysical : ∀ i phi,
      Integrable
          (fun x ↦ Complex.ofReal (F x i) * inverseFourierSchwartz phi x)
          volume ∧
        L i phi =
          ∫ x, Complex.ofReal (F x i) * inverseFourierSchwartz phi x ∂volume)
    (cells : Finset ι) (cellVolume : ι → ℝ)
    (localNegative : Fin d → ι → ℝ)
    (localTest : SchwartzMap (Vec d) ℂ → ι → ℝ)
    (pairingRe pairingIm :
      Fin d → SchwartzMap (Vec d) ℂ → ι → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hvolume : ∀ a ∈ cells, 0 ≤ cellVolume a)
    (hnegative : ∀ (i : Fin d) (a : ι), a ∈ cells →
      0 ≤ localNegative i a)
    (htestNonneg : ∀ (phi : SchwartzMap (Vec d) ℂ) (a : ι), a ∈ cells →
      0 ≤ localTest phi a)
    (hpairRe : ∀ (i : Fin d) (phi : SchwartzMap (Vec d) ℂ) (a : ι),
      a ∈ cells →
      |pairingRe i phi a| ≤ localNegative i a * localTest phi a)
    (hpairIm : ∀ (i : Fin d) (phi : SchwartzMap (Vec d) ℂ) (a : ι),
      a ∈ cells →
      |pairingIm i phi a| ≤ localNegative i a * localTest phi a)
    (hpositive : ∀ phi,
      fluxRowLocalTestSumSq cells cellVolume (localTest phi) ≤
        K * ‖fluxRowWeightedTestToLp volume
          (fluxRowMassiveTestDensity R sigma) (fluxRowSchwartzTestLinear d)
          htestMem phi‖ ^ 2)
    (hLRe : ∀ i phi,
      (L i phi).re =
        fluxRowLocalizedPairing cells cellVolume (pairingRe i phi))
    (hLIm : ∀ i phi,
      (L i phi).im =
        fluxRowLocalizedPairing cells cellVolume (pairingIm i phi))
    (C : Fin d → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hcoefficient : ∀ i,
      Real.sqrt
          (2 * K *
            fluxRowLocalNegativeSumSq cells cellVolume (localNegative i)) ≤
        C i) :
    ∃ fluxHat : Vec d → Fin d → ℂ,
      IsFourierRepresentative F fluxHat ∧
      massiveNegativeSobolevNormSq R sigma fluxHat ≤ ∑ i, C i ^ 2 := by
  apply exists_fluxHat_massiveNegativeSobolevNormSq_le_of_schwartz_bound hR F
    htestMem L hphysical C hC
  intro i phi
  let globalTest := ‖fluxRowWeightedTestToLp volume
    (fluxRowMassiveTestDensity R sigma) (fluxRowSchwartzTestLinear d)
    htestMem phi‖
  calc
    ‖L i phi‖ ≤
        Real.sqrt
            (2 * K *
              fluxRowLocalNegativeSumSq cells cellVolume (localNegative i)) *
          globalTest :=
      norm_complex_fluxRowDeterministicLocalization_le cells cellVolume
        (localNegative i) (localTest phi) (pairingRe i phi) (pairingIm i phi)
        globalTest K hK (norm_nonneg _) hvolume (hnegative i)
        (htestNonneg phi) (hpairRe i phi) (hpairIm i phi) (hpositive phi)
        (L i phi) (hLRe i phi) (hLIm i phi)
    _ ≤ C i * globalTest :=
      mul_le_mul_of_nonneg_right (hcoefficient i) (norm_nonneg _)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
