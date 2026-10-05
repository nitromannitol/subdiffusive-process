module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszLocalization

@[expose] public section

/-!
# Riesz construction along a stopping-partition exhaustion

An unbounded, locally finite stopping partition is used through finite
subfamilies.  This file proves the limit passage: uniform localization on the
finite subfamilies and convergence of their physical pairings give the global
Schwartz bound, hence the weighted Fourier-space Riesz representative.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Homogenization Topology
open _root_.SubdiffusiveProcess.Section8
open scoped BigOperators

noncomputable section

variable {ι : Type*}

/-- Uniform deterministic localization passes to the limit of a finite-cell
exhaustion. -/
theorem norm_complex_fluxRowDeterministicLocalization_limit_le
    (cells : ℕ → Finset ι) (volume localNegative localTest : ι → ℝ)
    (pairingRe pairingIm : ι → ℝ) (globalTest K C : ℝ)
    (hK : 0 ≤ K) (hglobalTest : 0 ≤ globalTest)
    (hvolume : ∀ n, ∀ a ∈ cells n, 0 ≤ volume a)
    (hnegative : ∀ n, ∀ a ∈ cells n, 0 ≤ localNegative a)
    (htest : ∀ n, ∀ a ∈ cells n, 0 ≤ localTest a)
    (hpairRe : ∀ n, ∀ a ∈ cells n,
      |pairingRe a| ≤ localNegative a * localTest a)
    (hpairIm : ∀ n, ∀ a ∈ cells n,
      |pairingIm a| ≤ localNegative a * localTest a)
    (hpositive : ∀ n,
      fluxRowLocalTestSumSq (cells n) volume localTest ≤
        K * globalTest ^ 2)
    (hcoefficient : ∀ n,
      Real.sqrt
          (2 * K *
            fluxRowLocalNegativeSumSq (cells n) volume localNegative) ≤ C)
    (z : ℂ)
    (hlimit : Tendsto
      (fun n ↦ Complex.mk
        (fluxRowLocalizedPairing (cells n) volume pairingRe)
        (fluxRowLocalizedPairing (cells n) volume pairingIm))
      atTop (𝓝 z)) :
    ‖z‖ ≤ C * globalTest := by
  have hnorm : Tendsto
      (fun n ↦ ‖Complex.mk
        (fluxRowLocalizedPairing (cells n) volume pairingRe)
        (fluxRowLocalizedPairing (cells n) volume pairingIm)‖)
      atTop (𝓝 ‖z‖) := hlimit.norm
  apply le_of_tendsto hnorm
  filter_upwards with n
  calc
    ‖Complex.mk
        (fluxRowLocalizedPairing (cells n) volume pairingRe)
        (fluxRowLocalizedPairing (cells n) volume pairingIm)‖ ≤
        Real.sqrt
            (2 * K *
              fluxRowLocalNegativeSumSq (cells n) volume localNegative) *
          globalTest :=
      norm_complex_fluxRowDeterministicLocalization_le (cells n) volume
        localNegative localTest pairingRe pairingIm globalTest K hK
        hglobalTest (hvolume n) (hnegative n) (htest n) (hpairRe n)
        (hpairIm n) (hpositive n) _ rfl rfl
    _ ≤ C * globalTest :=
      mul_le_mul_of_nonneg_right (hcoefficient n) hglobalTest

/-- The complete abstract stopping-partition endpoint.  A locally finite
partition is represented by finite exhausting families `cells n`; convergence
of the reconstructed cell pairings identifies their limit with the physical
Schwartz functional. -/
theorem exists_fluxHat_massiveNegativeSobolevNormSq_le_of_stopping_exhaustion
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
    (cells : ℕ → Finset ι) (cellVolume : ι → ℝ)
    (localNegative : Fin d → ι → ℝ)
    (localTest : SchwartzMap (Vec d) ℂ → ι → ℝ)
    (pairingRe pairingIm :
      Fin d → SchwartzMap (Vec d) ℂ → ι → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hvolume : ∀ n, ∀ a ∈ cells n, 0 ≤ cellVolume a)
    (hnegative : ∀ n, ∀ (i : Fin d), ∀ a ∈ cells n,
      0 ≤ localNegative i a)
    (htestNonneg : ∀ n, ∀ (phi : SchwartzMap (Vec d) ℂ), ∀ a ∈ cells n,
      0 ≤ localTest phi a)
    (hpairRe : ∀ n, ∀ (i : Fin d) (phi : SchwartzMap (Vec d) ℂ),
      ∀ a ∈ cells n,
      |pairingRe i phi a| ≤ localNegative i a * localTest phi a)
    (hpairIm : ∀ n, ∀ (i : Fin d) (phi : SchwartzMap (Vec d) ℂ),
      ∀ a ∈ cells n,
      |pairingIm i phi a| ≤ localNegative i a * localTest phi a)
    (hpositive : ∀ n phi,
      fluxRowLocalTestSumSq (cells n) cellVolume (localTest phi) ≤
        K * ‖fluxRowWeightedTestToLp volume
          (fluxRowMassiveTestDensity R sigma) (fluxRowSchwartzTestLinear d)
          htestMem phi‖ ^ 2)
    (C : Fin d → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hcoefficient : ∀ n i,
      Real.sqrt
          (2 * K *
            fluxRowLocalNegativeSumSq (cells n) cellVolume
              (localNegative i)) ≤ C i)
    (hlimit : ∀ i phi, Tendsto
      (fun n ↦ Complex.mk
        (fluxRowLocalizedPairing (cells n) cellVolume (pairingRe i phi))
        (fluxRowLocalizedPairing (cells n) cellVolume (pairingIm i phi)))
      atTop (𝓝 (L i phi))) :
    ∃ fluxHat : Vec d → Fin d → ℂ,
      IsFourierRepresentative F fluxHat ∧
      massiveNegativeSobolevNormSq R sigma fluxHat ≤ ∑ i, C i ^ 2 := by
  apply exists_fluxHat_massiveNegativeSobolevNormSq_le_of_schwartz_bound hR F
    htestMem L hphysical C hC
  intro i phi
  let globalTest := ‖fluxRowWeightedTestToLp volume
    (fluxRowMassiveTestDensity R sigma) (fluxRowSchwartzTestLinear d)
    htestMem phi‖
  exact norm_complex_fluxRowDeterministicLocalization_limit_le cells cellVolume
    (localNegative i) (localTest phi) (pairingRe i phi) (pairingIm i phi)
    globalTest K (C i) hK (norm_nonneg _) hvolume
    (fun n ↦ hnegative n i) (fun n ↦ htestNonneg n phi)
    (fun n ↦ hpairRe n i phi) (fun n ↦ hpairIm n i phi)
    (fun n ↦ hpositive n phi) (fun n ↦ hcoefficient n i) (L i phi)
    (hlimit i phi)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
