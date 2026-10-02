import SubdiffusiveProcess.Providers.Section2.GeneralCoarseGraining

/-!
# Smooth-dual general coarse-graining assembly

The finite-`p` library assembly of
`SubdiffusiveProcess.Providers.Section2.exists_generalCoarseGraining_paperDual_libraryRHS`,
stopped at the library smooth negative dual: the CZ comparison, the descendant
smooth-dual/negative-Besov aggregation and the local coarse-graining bound are
chained directly, without the paper-dual conversion factor
`K = s ^ (-1 / p')`.
-/

namespace SubdiffusiveProcess.Providers.Section2.SmoothDualScratch

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03.ABK26 MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- Local copy of the private scale-weight cancellation in
`GeneralCoarseGraining.lean`. -/
theorem aux_ofReal_three_rpow_scale_triple (s : ℝ) (m n : ℤ) :
    ENNReal.ofReal (Real.rpow 3 (-s * (m : ℝ))) *
        ENNReal.ofReal (Real.rpow 3 (s * (((m - n : ℤ) : ℝ)))) *
      ENNReal.ofReal (Real.rpow 3 (s * (n : ℝ))) = 1 := by exact SubdiffusiveProcess.Providers.Section2.aux_dedup_d158_ofReal_three_rpow_scale_triple (s := s) (m := m) (n := n)

/-- Local copy of the private constant absorption in
`GeneralCoarseGraining.lean`. -/
theorem aux_localCoarseGrainingLpRHS_const_mul {d : ℕ} [NeZero d]
    (K C : ℝ≥0∞) (Q : Homogenization.TriadicCube d)
    (n : ℤ) (hn : n ≤ Q.scale)
    (a : Ch02.CoeffOn (Ch02.cubeDomain Q)) (sigma0 : ℝ)
    (hsigma0 : 0 < sigma0)
    (g : Homogenization.Vec d → Homogenization.Vec d)
    (u : H1Function (openCubeSet Q)) (s1 s s2 : FractionalOrder)
    (p : FiniteLpExponent) :
    K * localCoarseGrainingLpRHS C Q n hn a sigma0 hsigma0 g u s1 s s2 p =
      localCoarseGrainingLpRHS (K * C) Q n hn a sigma0 hsigma0 g u s1 s s2 p := by exact SubdiffusiveProcess.Providers.Section2.aux_dedup_d071_localCoarseGrainingLpRHS_const_mul (d := d) (K := K) (C := C) (Q := Q) (n := n) (hn := hn) (a := a) (sigma0 := sigma0) (hsigma0 := hsigma0) (g := g) (u := u) (s1 := s1) (s := s) (s2 := s2) (p := p)

/-- The finite-`p` general coarse-graining assembly in the library smooth
negative dual: no paper-dual conversion factor appears. -/
theorem exists_generalCoarseGraining_smoothDual_libraryRHS
    (d : ℕ) (hd : 2 ≤ d) (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) ≤ p.exponent) :
    letI : NeZero d := ⟨by omega⟩
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (m n : ℤ) (hnm : n < m) (s1 s s2 : FractionalOrder),
        s1.1 < s.1 → s.1 < s2.1 →
      ∀ (a : Ch02.CoeffOn (Ch02.cubeDomain (originCube d m)))
        (sigma0 : ℝ) (hsigma0 : 0 < sigma0)
        (g : Homogenization.Vec d → Homogenization.Vec d),
        MemCubeEuclideanFullWsp (originCube d m) s2 p g →
      ∀ u v : H1Function (openCubeSet (originCube d m)),
        IsForcedEquation (originCube d m) a u g →
        IsScalarForcedEquation (originCube d m) sigma0 v g →
        HasH10Difference (originCube d m) u v →
        ENNReal.ofReal (Real.rpow 3 (-s.1 * (m : ℝ))) *
            (ENNReal.ofReal sigma0 * cubeEuclideanNegativeWspSmoothDualENorm
                (originCube d m) s p (centeredCubeGradientDifferenceL2Field m u v) +
              cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p
                (centeredCubeFluxDifferenceL2Field m a sigma0 u v)) ≤
          localCoarseGrainingLpRHS C (originCube d m) n
            (by simpa [originCube] using hnm.le) a sigma0 hsigma0
            g u s1 s s2 p := by
  letI : NeZero d := ⟨by omega⟩
  obtain ⟨Ccz, hCczTop, hCcz⟩ := exists_centeredCubeFluxComparison_cz d hd p hp
  obtain ⟨Clc, hClcTop, hClc⟩ := exists_localCoarseGrainingLp d hd
  let Cd := cubeEuclideanNegativeWspSmoothDualBesovConstant d
  refine ⟨Ccz * Cd * Clc, ?_, ?_⟩
  · exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top hCczTop
        (cubeEuclideanNegativeWspSmoothDualBesovConstant_lt_top d)) hClcTop
  intro m n hnm s1 s s2 hs1s hss2 a sigma0 hsigma0 g hg u v hu hv hzero
  have hn : n ≤ (originCube d m).scale := by simpa [originCube] using hnm.le
  have hbal := isCenteredCubeFluxBalanced_of_forced a hu hv
  have hcz := hCcz m n hnm a sigma0 hsigma0 s u v hbal hzero
  have hmiddle := localFluxDefect_smoothDualAverage_le hnm hn a sigma0 u s p
  have hlocal := hClc p hp m n hnm s1 s s2 hs1s hss2
    a sigma0 hsigma0 g hg u hu
  let W : ℝ≥0∞ := ENNReal.ofReal (Real.rpow 3 (-s.1 * (m : ℝ)))
  let Wmn : ℝ≥0∞ := ENNReal.ofReal
    (Real.rpow 3 (s.1 * (((m - n : ℤ) : ℝ))))
  let Wn : ℝ≥0∞ := ENNReal.ofReal (Real.rpow 3 (s.1 * (n : ℝ)))
  have htriple : W * Wmn * Wn = 1 := aux_ofReal_three_rpow_scale_triple s.1 m n
  change W * centeredCubeFluxComparisonSmoothDualLHS m a sigma0 u v s p ≤ _
  calc
    W * centeredCubeFluxComparisonSmoothDualLHS m a sigma0 u v s p ≤
        W * (Ccz * Wmn *
          centeredCubeLocalFluxDefectSmoothDualLpAverage
            m n hnm a sigma0 u s p) := by gcongr
    _ ≤ W * (Ccz * Wmn * (Cd * Wn *
          localFluxDefectNegativeBesovLpAverage
            (originCube d m) n hn a sigma0 u s p)) := by gcongr
    _ = Ccz * Cd *
          localFluxDefectNegativeBesovLpAverage
            (originCube d m) n hn a sigma0 u s p := by
          calc
            W * (Ccz * Wmn * (Cd * Wn *
                localFluxDefectNegativeBesovLpAverage
                  (originCube d m) n hn a sigma0 u s p)) =
                (W * Wmn * Wn) *
                  (Ccz * Cd * localFluxDefectNegativeBesovLpAverage
                    (originCube d m) n hn a sigma0 u s p) := by ring
            _ = _ := by rw [htriple, one_mul]
    _ ≤ Ccz * Cd *
          localCoarseGrainingLpRHS Clc (originCube d m) n hn
            a sigma0 hsigma0 g u s1 s s2 p := by gcongr
    _ = localCoarseGrainingLpRHS (Ccz * Cd * Clc)
          (originCube d m) n hn a sigma0 hsigma0 g u s1 s s2 p := by
          rw [aux_localCoarseGrainingLpRHS_const_mul]

/-- The `p = 2` specialization. -/
theorem exists_generalCoarseGraining_smoothDual_libraryRHS_two
    (d : ℕ) (hd : 2 ≤ d) :
    letI : NeZero d := ⟨by omega⟩
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (m n : ℤ) (hnm : n < m) (s1 s s2 : FractionalOrder),
        s1.1 < s.1 → s.1 < s2.1 →
      ∀ (a : Ch02.CoeffOn (Ch02.cubeDomain (originCube d m)))
        (sigma0 : ℝ) (hsigma0 : 0 < sigma0)
        (g : Homogenization.Vec d → Homogenization.Vec d),
        MemCubeEuclideanFullWsp (originCube d m) s2 FiniteLpExponent.two g →
      ∀ u v : H1Function (openCubeSet (originCube d m)),
        IsForcedEquation (originCube d m) a u g →
        IsScalarForcedEquation (originCube d m) sigma0 v g →
        HasH10Difference (originCube d m) u v →
        ENNReal.ofReal (Real.rpow 3 (-s.1 * (m : ℝ))) *
            (ENNReal.ofReal sigma0 * cubeEuclideanNegativeWspSmoothDualENorm
                (originCube d m) s FiniteLpExponent.two
                (centeredCubeGradientDifferenceL2Field m u v) +
              cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s
                FiniteLpExponent.two
                (centeredCubeFluxDifferenceL2Field m a sigma0 u v)) ≤
          localCoarseGrainingLpRHS C (originCube d m) n
            (by simpa [originCube] using hnm.le) a sigma0 hsigma0
            g u s1 s s2 FiniteLpExponent.two :=
  exists_generalCoarseGraining_smoothDual_libraryRHS d hd FiniteLpExponent.two
    (by simp)

end

end SubdiffusiveProcess.Providers.Section2.SmoothDualScratch


