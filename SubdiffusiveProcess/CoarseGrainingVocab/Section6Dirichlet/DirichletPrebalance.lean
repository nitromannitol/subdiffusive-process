module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.CoarseGrainingRHS
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.EnergyPartition
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.PaperNegativeDualDilation

@[expose] public section

/-!
# The rescaled Dirichlet prebalance estimate

The general coarse-graining theorem is stated on the physical centered cube.
This file performs the exact negative-dual dilation back to the unit cube.
The gradient and normalized-flux amplitudes look different before dilation,
but both acquire the same factor `3^m / alpha` after the two physical terms
are compared with the coarse-graining left-hand side.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

private theorem ofReal_centeredCubeScale_rpow_neg_natCast
    (N : ℕ) (s : ℝ) :
    (ENNReal.ofReal (centeredCubeScale (N : ℤ))) ^ (-s) =
      ENNReal.ofReal (Real.rpow 3 (-s * (N : ℝ))) := by
  rw [ENNReal.ofReal_rpow_of_pos (centeredCubeScale_pos (N : ℤ))]
  congr 1
  simp only [centeredCubeScale, zpow_natCast]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

/-- At `p = 2`, the weighted descendant energy is exactly the square root
of the geometric-series mass times the parent normalized energy.  This is
the direct (unsquared) carrier used in the Dirichlet prebalance row. -/
theorem weightedLocalSymmetricEnergyLp_two_eq
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (n : ℤ)
    (hn : n ≤ Q.scale) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (u : H1Function (openCubeSet Q)) (s1 s : FractionalOrder)
    (hgap : 0 < s.1 - s1.1) :
    weightedLocalSymmetricEnergyLp Q n hn a u s1 s
        FiniteLpExponent.two =
      (ENNReal.ofReal
          ((Ch02.geometricDiscount (2 * (s.1 - s1.1)) 1)⁻¹)) ^
          (1 / 2 : ℝ) * localSymmetricEnergyENorm Q a u := by
  let W := weightedLocalSymmetricEnergyLp Q n hn a u s1 s
    FiniteLpExponent.two
  let A : ℝ≥0∞ := ENNReal.ofReal
    ((Ch02.geometricDiscount (2 * (s.1 - s1.1)) 1)⁻¹)
  let E := localSymmetricEnergyENorm Q a u
  have hsq : W ^ (2 : ℕ) = A * E ^ (2 : ℕ) := by
    exact weightedLocalSymmetricEnergyLp_two_sq_eq Q n hn a u s1 s hgap
  have hhalf := congrArg (fun z : ℝ≥0∞ ↦ z ^ (1 / 2 : ℝ)) hsq
  change W = A ^ (1 / 2 : ℝ) * E
  calc
    W = (W ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    _ = (A * E ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := hhalf
    _ = A ^ (1 / 2 : ℝ) * (E ^ (2 : ℕ)) ^ (1 / 2 : ℝ) :=
      ENNReal.mul_rpow_of_nonneg A (E ^ (2 : ℕ)) (by norm_num)
    _ = A ^ (1 / 2 : ℝ) * E := by
      congr 1
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num

/-- Bound form of `weightedLocalSymmetricEnergyLp_two_eq`, ready for the
real carrier slot of the coarse-graining application. -/
theorem weightedLocalSymmetricEnergyLp_two_le_of_parent_le
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (n : ℤ)
    (hn : n ≤ Q.scale) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (u : H1Function (openCubeSet Q)) (s1 s : FractionalOrder)
    (hgap : 0 < s.1 - s1.1) {S : ℝ}
    (hparent : localSymmetricEnergyENorm Q a u ≤ ENNReal.ofReal S) :
    weightedLocalSymmetricEnergyLp Q n hn a u s1 s
        FiniteLpExponent.two ≤
      (ENNReal.ofReal
          ((Ch02.geometricDiscount (2 * (s.1 - s1.1)) 1)⁻¹)) ^
          (1 / 2 : ℝ) * ENNReal.ofReal S := by
  rw [weightedLocalSymmetricEnergyLp_two_eq Q n hn a u s1 s hgap]
  exact mul_le_mul_right hparent _

/-- Finite real spelling of the geometric partition factor. -/
noncomputable def dirichletWeightedEnergyFactor (s1 s : ℝ) : ℝ :=
  ((ENNReal.ofReal
      ((Ch02.geometricDiscount (2 * (s - s1)) 1)⁻¹)) ^
        (1 / 2 : ℝ)).toReal

theorem dirichletWeightedEnergyFactor_nonneg (s1 s : ℝ) :
    0 ≤ dirichletWeightedEnergyFactor s1 s := ENNReal.toReal_nonneg

/-- Real-bound form of the parent-energy partition row. -/
theorem weightedLocalSymmetricEnergyLp_two_le_realBound
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (n : ℤ)
    (hn : n ≤ Q.scale) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (u : H1Function (openCubeSet Q)) (s1 s : FractionalOrder)
    (hgap : 0 < s.1 - s1.1) {S : ℝ}
    (hparent : localSymmetricEnergyENorm Q a u ≤ ENNReal.ofReal S) :
    weightedLocalSymmetricEnergyLp Q n hn a u s1 s
        FiniteLpExponent.two ≤
      ENNReal.ofReal (dirichletWeightedEnergyFactor s1.1 s.1 * S) := by
  let A : ℝ≥0∞ :=
    (ENNReal.ofReal
      ((Ch02.geometricDiscount (2 * (s.1 - s1.1)) 1)⁻¹)) ^
        (1 / 2 : ℝ)
  have hAtop : A ≠ ∞ := by
    exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top).ne
  have hmain := weightedLocalSymmetricEnergyLp_two_le_of_parent_le
    Q n hn a u s1 s hgap hparent
  calc
    _ ≤ A * ENNReal.ofReal S := by simpa only [A] using hmain
    _ = ENNReal.ofReal (dirichletWeightedEnergyFactor s1.1 s.1 * S) := by
      rw [show A = ENNReal.ofReal A.toReal by
        exact (ENNReal.ofReal_toReal hAtop).symm]
      calc
        ENNReal.ofReal A.toReal * ENNReal.ofReal S =
            ENNReal.ofReal (A.toReal * S) :=
          (ENNReal.ofReal_mul ENNReal.toReal_nonneg).symm
        _ = ENNReal.ofReal (dirichletWeightedEnergyFactor s1.1 s.1 * S) := by
          rfl

/-- Exact unit-cube readout of a physical centered-cube coarse-graining
estimate.  This is the normalization calculation in
`e.Dirichlet.prebalance`: both negative fractional duals pay the same
`3^m / alpha` factor. -/
theorem unitPaperNegativeDualSum_le_of_physicalCoarseGraining
    {d : ℕ} (m : ℤ) {alpha : ℝ} (halpha : 0 < alpha)
    (s : FractionalOrder)
    (Fgrad Fflux : CubeEuclideanLpField
      (originCube d m) FiniteLpExponent.two)
    {B : ℝ}
    (hphysical :
      (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
            ENNReal.ofReal alpha *
            paperNegativeFractionalDual (originCube d m) s
              FiniteLpExponent.two Fgrad +
          (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
            paperNegativeFractionalDual (originCube d m) s
              FiniteLpExponent.two Fflux ≤
        ENNReal.ofReal B) :
    paperNegativeFractionalDual (originCube d 0) s
          FiniteLpExponent.two
          (scaledCenteredCubePullbackEuclideanL2Field m
            (centeredCubeScale m) Fgrad) +
        paperNegativeFractionalDual (originCube d 0) s
          FiniteLpExponent.two
          (scaledCenteredCubePullbackEuclideanL2Field m
            (centeredCubeScale m * alpha⁻¹) Fflux) ≤
      ENNReal.ofReal (centeredCubeScale m * alpha⁻¹ * B) := by
  let R : ℝ := centeredCubeScale m
  let A : ℝ≥0∞ := (ENNReal.ofReal R) ^ (-s.1)
  let K : ℝ≥0∞ := ENNReal.ofReal (R * alpha⁻¹)
  let Dg : ℝ≥0∞ := paperNegativeFractionalDual (originCube d m) s
    FiniteLpExponent.two Fgrad
  let Df : ℝ≥0∞ := paperNegativeFractionalDual (originCube d m) s
    FiniteLpExponent.two Fflux
  have hR : 0 < R := centeredCubeScale_pos m
  have hKreal : 0 ≤ R * alpha⁻¹ := mul_nonneg hR.le (inv_nonneg.mpr halpha.le)
  have hKR : K * ENNReal.ofReal alpha = ENNReal.ofReal R := by
    dsimp only [K]
    rw [← ENNReal.ofReal_mul hKreal]
    congr 1
    field_simp [halpha.ne']
  have hRnorm : ‖R‖ₑ = ENNReal.ofReal R := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_pos hR]
  have hKnorm : ‖R * alpha⁻¹‖ₑ = K := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hKreal]
  have hg := paperNegativeFractionalDual_scaledCenteredCubePullback_le
    m R s FiniteLpExponent.two Fgrad
  have hf := paperNegativeFractionalDual_scaledCenteredCubePullback_le
    m (R * alpha⁻¹) s FiniteLpExponent.two Fflux
  change A * ENNReal.ofReal alpha * Dg + A * Df ≤ ENNReal.ofReal B at hphysical
  change
    paperNegativeFractionalDual (originCube d 0) s FiniteLpExponent.two
          (scaledCenteredCubePullbackEuclideanL2Field m R Fgrad) +
        paperNegativeFractionalDual (originCube d 0) s FiniteLpExponent.two
          (scaledCenteredCubePullbackEuclideanL2Field m (R * alpha⁻¹) Fflux) ≤
      ENNReal.ofReal (R * alpha⁻¹ * B)
  calc
    _ ≤ ‖R‖ₑ * A * Dg + ‖R * alpha⁻¹‖ₑ * A * Df :=
      add_le_add hg hf
    _ = K * (A * ENNReal.ofReal alpha * Dg + A * Df) := by
      rw [hRnorm, hKnorm, ← hKR]
      ring
    _ ≤ K * ENNReal.ofReal B := mul_le_mul_right hphysical K
    _ = ENNReal.ofReal (R * alpha⁻¹ * B) := by
      dsimp only [K]
      rw [ENNReal.ofReal_mul hKreal]

/-- The `p = 2` coarse-graining theorem at the manuscript's mesoscopic
index `N-k`, with both response tails replaced by the full errors at `N`,
followed by the exact dilation to the unit cube.  The remaining four real
bounds are precisely the response, energy, and positive-datum rows supplied
by the neighboring Dirichlet support modules. -/
theorem exists_unit_dirichletPrebalance_of_carrier_bounds
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N k : ℕ), 0 < k →
        ∀ (a : Ch02.TriadicCoeffFamily d),
          (∀ Q, Ch02.CoeffOn.IsSymmetric (a.coeffOn Q)) →
        ∀ (alpha s s1 s2 : ℝ), 0 < alpha →
          ∀ hs1pos : 0 < s1, ∀ hs1s : s1 < s,
          ∀ hss2 : s < s2, ∀ hs2one : s2 < 1,
          ∀ (hs : FractionalOrder), hs.1 = s →
          ∀ (hs2 : FractionalOrder), hs2.1 = s2 →
          ∀ g : CubeEuclideanWspField (originCube d (N : ℤ)) hs2
              FiniteLpExponent.two,
          ∀ u v : H1Function (openCubeSet (originCube d (N : ℤ))),
            IsForcedEquation (originCube d (N : ℤ))
                (a.coeffOn (originCube d (N : ℤ))) u g.toField →
            IsScalarForcedEquation (originCube d (N : ℤ)) alpha v g.toField →
            HasH10Difference (originCube d (N : ℤ)) u v →
          ∀ E1 E2 S D : ℝ, 0 ≤ E1 → 0 ≤ E2 → 0 ≤ S → 0 ≤ D →
            paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ) s1
                .infinity (.finite 1) a alpha ≤ ENNReal.ofReal E1 →
            paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ) (s1 / 2)
                .infinity (.finite 2) a alpha ≤ ENNReal.ofReal E2 →
            weightedLocalSymmetricEnergyLp (originCube d (N : ℤ))
                ((N : ℤ) - (k : ℤ)) (by simp [originCube])
                (a.coeffOn (originCube d (N : ℤ))) u
                ⟨s1, hs1pos, by linarith⟩ hs FiniteLpExponent.two ≤
              ENNReal.ofReal S →
            paperFractionalSeminorm (originCube d (N : ℤ)) hs2
                FiniteLpExponent.two g.toField ≤ ENNReal.ofReal D →
            paperNegativeFractionalDual (originCube d 0) hs
                  FiniteLpExponent.two
                  (scaledCenteredCubePullbackEuclideanL2Field (N : ℤ)
                    (centeredCubeScale (N : ℤ))
                    (centeredCubeGradientDifferenceL2Field (N : ℤ) u v)) +
                paperNegativeFractionalDual (originCube d 0) hs
                  FiniteLpExponent.two
                  (scaledCenteredCubePullbackEuclideanL2Field (N : ℤ)
                    (centeredCubeScale (N : ℤ) * alpha⁻¹)
                    (centeredCubeFluxDifferenceL2Field (N : ℤ)
                      (a.coeffOn (originCube d (N : ℤ))) alpha u v)) ≤
              ENNReal.ofReal
                (centeredCubeScale (N : ℤ) * alpha⁻¹ *
                  dirichletCoarseGrainingRHS C alpha s s2
                    (Real.rpow 3 (s1 * (k : ℝ)) * E1)
                    (Real.rpow 3 ((s1 / 2) * (k : ℝ)) * E2)
                    S D ((N : ℤ) - (k : ℤ))) := by
  obtain ⟨C, hC, hcg⟩ := exists_generalCoarseGraining_two_le_dirichletRHS d hd
  refine ⟨C, hC, ?_⟩
  intro N k hk a ha alpha s s1 s2 halpha hs1pos hs1s hss2 hs2one
    hs hhs hs2 hhs2 g u v hu hv huv E1 E2 S D hE10 hE20 hS0 hD0
    hE1 hE2 hS hD
  let E1k : ℝ := Real.rpow 3 (s1 * (k : ℝ)) * E1
  let E2k : ℝ := Real.rpow 3 ((s1 / 2) * (k : ℝ)) * E2
  have hE1k0 : 0 ≤ E1k :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) hE10
  have hE2k0 : 0 ≤ E2k :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) hE20
  have hE1trunc :
      paperHomogenizationError (originCube d (N : ℤ))
          ((N : ℤ) - (k : ℤ)) s1 .infinity (.finite 1) a alpha ≤
        ENNReal.ofReal E1k := by
    calc
      _ ≤ ENNReal.ofReal (Real.rpow 3 (s1 * (k : ℝ))) *
          paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ) s1
            .infinity (.finite 1) a alpha :=
        paperHomogenizationError_sub_natCast_infinity_one_le
          (originCube d (N : ℤ)) (N : ℤ) k a alpha
      _ ≤ ENNReal.ofReal (Real.rpow 3 (s1 * (k : ℝ))) *
          ENNReal.ofReal E1 := mul_le_mul_right hE1 _
      _ = ENNReal.ofReal E1k := by
        dsimp only [E1k]
        exact (ENNReal.ofReal_mul
          (p := Real.rpow 3 (s1 * (k : ℝ))) (q := E1)
          (Real.rpow_nonneg (by norm_num) _)).symm
  have hE2trunc :
      paperHomogenizationError (originCube d (N : ℤ))
          ((N : ℤ) - (k : ℤ)) (s1 / 2) .infinity (.finite 2) a alpha ≤
        ENNReal.ofReal E2k := by
    calc
      _ ≤ ENNReal.ofReal (Real.rpow 3 ((s1 / 2) * (k : ℝ))) *
          paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ) (s1 / 2)
            .infinity (.finite 2) a alpha :=
        paperHomogenizationError_sub_natCast_infinity_two_le
          (originCube d (N : ℤ)) (N : ℤ) k a alpha
      _ ≤ ENNReal.ofReal (Real.rpow 3 ((s1 / 2) * (k : ℝ))) *
          ENNReal.ofReal E2 := mul_le_mul_right hE2 _
      _ = ENNReal.ofReal E2k := by
        dsimp only [E2k]
        exact (ENNReal.ofReal_mul
          (p := Real.rpow 3 ((s1 / 2) * (k : ℝ))) (q := E2)
          (Real.rpow_nonneg (by norm_num) _)).symm
  have hnm : (N : ℤ) - (k : ℤ) < (N : ℤ) := by omega
  have hphysical := hcg (N : ℤ) ((N : ℤ) - (k : ℤ)) hnm a ha
    alpha s s1 s2 halpha hs1pos hs1s hss2 hs2one hs hhs hs2 hhs2
    g u v hu hv huv E1k E2k S D hE1k0 hE2k0 hS0 hD0
    hE1trunc hE2trunc hS hD
  have hscale := ofReal_centeredCubeScale_rpow_neg_natCast N s
  have hphysical' :
      (ENNReal.ofReal (centeredCubeScale (N : ℤ))) ^ (-hs.1) *
            ENNReal.ofReal alpha *
            paperNegativeFractionalDual (originCube d (N : ℤ)) hs
              FiniteLpExponent.two
              (centeredCubeGradientDifferenceL2Field (N : ℤ) u v) +
          (ENNReal.ofReal (centeredCubeScale (N : ℤ))) ^ (-hs.1) *
            paperNegativeFractionalDual (originCube d (N : ℤ)) hs
              FiniteLpExponent.two
              (centeredCubeFluxDifferenceL2Field (N : ℤ)
                (a.coeffOn (originCube d (N : ℤ))) alpha u v) ≤
        ENNReal.ofReal (dirichletCoarseGrainingRHS C alpha s s2
          E1k E2k S D ((N : ℤ) - (k : ℤ))) := by
    rw [hhs, hscale]
    simp only [Int.cast_natCast] at hphysical
    simpa only [ENNReal.ofReal_mul
      (p := Real.rpow 3 (-s * (N : ℝ))) (q := alpha)
      (Real.rpow_nonneg (by norm_num) _)] using hphysical
  simpa only [E1k, E2k] using
    unitPaperNegativeDualSum_le_of_physicalCoarseGraining
      (N : ℤ) halpha hs
      (centeredCubeGradientDifferenceL2Field (N : ℤ) u v)
      (centeredCubeFluxDifferenceL2Field (N : ℤ)
        (a.coeffOn (originCube d (N : ℤ))) alpha u v)
      hphysical'

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
