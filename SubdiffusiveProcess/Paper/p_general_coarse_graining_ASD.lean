module

public import SubdiffusiveProcess.Frozen.Section2.GeneralCoarseGraining

@[expose] public section




open SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem p_general_coarse_graining_ASD {d : ℕ}
    (p : Homogenization.FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) ≤ p.exponent) :
    ∀ hd : 2 ≤ d, ∃ C : ℝ, 0 < C ∧
      ∀ (m n : ℤ), ∀ hnm : n < m,
        ∀ (a : Ch02.TriadicCoeffFamily d),
          (∀ Q, Ch02.CoeffOn.IsSymmetric (a.coeffOn Q)) →
          ∀ (alpha s s1 s2 : ℝ), 0 < alpha →
            ∀ hs1pos : 0 < s1, ∀ hs1s : s1 < s,
              ∀ hss2 : s < s2, ∀ hs2one : s2 < 1,
              ∀ hsp : s * p.conjugate.exponent.toReal < 1,
            ∀ (hs : Homogenization.FractionalOrder)
              (hhs : hs.1 = s)
              (hs2 : Homogenization.FractionalOrder)
              (hhs2 : hs2.1 = s2),
              ∀ g : Homogenization.CubeEuclideanWspField
                  (Homogenization.originCube d m) hs2 p,
                ∀ u v : Homogenization.H1Function
                    (Homogenization.openCubeSet (Homogenization.originCube d m)),
                  Homogenization.Book.Ch03.ABK26.IsForcedEquation
                      (Homogenization.originCube d m)
                      (a.coeffOn (Homogenization.originCube d m)) u g.toField →
                  Homogenization.Book.Ch03.ABK26.IsScalarForcedEquation
                      (Homogenization.originCube d m) alpha v g.toField →
                  Homogenization.Book.Ch03.ABK26.HasH10Difference
                      (Homogenization.originCube d m) u v →
                  ENNReal.ofReal (Real.rpow 3 (-s * (m : ℝ)) * alpha) *
                        paperNegativeFractionalDual
                          (Homogenization.originCube d m) hs p
                          (Homogenization.Book.Ch03.ABK26.centeredCubeGradientDifferenceL2Field
                            m u v) +
                      ENNReal.ofReal (Real.rpow 3 (-s * (m : ℝ))) *
                        paperNegativeFractionalDual
                          (Homogenization.originCube d m) hs p
                          (Homogenization.Book.Ch03.ABK26.centeredCubeFluxDifferenceL2Field
                            m (a.coeffOn (Homogenization.originCube d m)) alpha u v) ≤
                    ENNReal.ofReal
                        (C * Real.rpow s
                          (-1 - (p.conjugate.exponent.toReal)⁻¹) * Real.sqrt alpha) *
                      paperHomogenizationError
                        (Homogenization.originCube d m) n s1 .infinity (.finite 1)
                        a alpha *
                      @Homogenization.Book.Ch03.ABK26.weightedLocalSymmetricEnergyLp d
                        ⟨by omega⟩
                        (Homogenization.originCube d m) n
                        (by simpa [Homogenization.originCube] using hnm.le)
                        (a.coeffOn (Homogenization.originCube d m)) u
                        ⟨s1, hs1pos, by linarith⟩ hs p +
                    ENNReal.ofReal
                        (C * Real.rpow s (-11 / 2) * (s2 - s)⁻¹ *
                          Real.rpow 3 (s2 * (n : ℝ))) *
                      (1 + paperHomogenizationError
                        (Homogenization.originCube d m) n (s1 / 2)
                        .infinity (.finite 2) a alpha ^ 2) *
                      paperFractionalSeminorm
                        (Homogenization.originCube d m) hs2 p g.toField := by
  intro hd
  obtain ⟨C, hC, h⟩ := SubdiffusiveProcess.Frozen.Section2.general_coarse_graining p hp hd
  refine ⟨C, hC, ?_⟩
  intro m n hnm a hsym alpha s s1 s2 halpha hs1pos hs1s hss2 hs2one _hsp hs hhs hs2 hhs2 g u v h1 h2 h3
  exact h m n hnm a hsym alpha s s1 s2 halpha hs1pos hs1s hss2 hs2one hs hhs hs2 hhs2 g u v h1 h2 h3

end Paper
