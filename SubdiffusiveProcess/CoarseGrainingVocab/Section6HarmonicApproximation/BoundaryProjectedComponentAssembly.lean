import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryProjectedCellComparisons
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryProjectedCellProfile
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryComparatorSharpErrorReplacement
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.DirichletPrebalance




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- The inhomogeneous finite-`p` fractional carrier is stable under removing
the cube-average vector. -/
theorem memCubeEuclideanFullWsp_cubeFluctuationVec
    {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder}
    {g : Vec d → Vec d}
    (hg : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two g) :
    Ch03.ABK26.MemCubeEuclideanFullWsp Q s FiniteLpExponent.two
      (cubeFluctuationVec Q g) := by
  refine ⟨?_, ?_⟩
  · have hsub := hg.1.sub (memLp_const (HilbertVec.ofVec (cubeAverageVec Q g)))
    simpa only [cubeFluctuationVec, Pi.sub_apply, map_sub] using hsub
  have hkernel : cubeEuclideanWspKernel s FiniteLpExponent.two
      (cubeFluctuationVec Q g) = cubeEuclideanWspKernel s FiniteLpExponent.two g := by
    funext z
    unfold cubeEuclideanWspKernel cubeFluctuationVec
    congr 1
    apply congrArg HilbertVec.ofVec
    funext i
    simp only [Pi.sub_apply]
    ring
  unfold MemCubeEuclideanWsp
  rw [hkernel]
  exact hg.2



theorem abk26IsForcedEquation_of_publicNeg
    {d : ℕ} {Q : TriadicCube d} {A : CoeffFamily d}
    {u : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hu : IsForcedEquation Q A u (fun x ↦ -g x)) :
    Ch03.ABK26.IsForcedEquation Q (A.coeffOn Q) u g := by
  intro phi
  have h := hu phi
  calc
    (∫ x in openCubeSet Q,
        vecDot (matVecMul ((A.coeffOn Q).toCoeffField x) (u.grad x))
          (phi.toH1Function.grad x) ∂volume) =
        ∫ x in openCubeSet Q,
          vecDot (-g x) (phi.toH1Function.grad x) ∂volume := h
    _ = -(∫ x in openCubeSet Q,
          vecDot (g x) (phi.toH1Function.grad x) ∂volume) := by
      simp_rw [vecDot_neg_left]
      rw [integral_neg]

/-- The weighted-energy premise in the sharp comparator is not an additional
moment input at `p=2`: it is the exact geometric factor times the square root
of the root normalized coefficient energy. -/
theorem weightedLocalSymmetricEnergyLp_two_le_rootEnergyReadout
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (u : H1Function (openCubeSet Q)) (s1 s : FractionalOrder)
    (hgap : 0 < s.1 - s1.1) :
    Ch03.ABK26.weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
        a u s1 s FiniteLpExponent.two ≤
      ENNReal.ofReal
        (Section6Dirichlet.dirichletWeightedEnergyFactor s1.1 s.1 *
          Real.sqrt (cubeAverage Q
            (coefficientEnergyDensity a.toCoeffField u.grad))) := by
  let E : ℝ := cubeAverage Q (coefficientEnergyDensity a.toCoeffField u.grad)
  have hparent : Ch03.ABK26.localSymmetricEnergyENorm Q a u ≤
      ENNReal.ofReal (Real.sqrt E) := by
    rw [Ch03.ABK26.localSymmetricEnergyENorm_eq_ofReal_cubeAverage_coefficientEnergyDensity]
    by_cases hE : 0 ≤ E
    · rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hE]
      norm_num
    · have hEle : E ≤ 0 := le_of_not_ge hE
      rw [ENNReal.ofReal_eq_zero.mpr hEle, Real.sqrt_eq_zero_of_nonpos hEle,
        ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
  simpa only [E] using
    Section6Dirichlet.weightedLocalSymmetricEnergyLp_two_le_realBound
      Q (Q.scale - 1) (by omega) a u s1 s hgap hparent

/-- The projected physical-cell endpoint after the common-gap comparison has
been assembled from its physical `L²`, positive-Besov, and Euclidean-`L²`
components.  The remaining `hU` premise is exactly the slot filled by a
noncircular parent/comparator estimate. -/
theorem exists_projectedBoundaryCellPhysicalEnergy_of_componentCaps
    (d : ℕ) [NeZero d] :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (s : ℝ), s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (sOrder : FractionalOrder), sOrder.1 = s →
      ∀ (L m n : ℕ), m ≤ L → n + 5 ≤ m →
      ∀ (z x q : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        omega ∈ goodEvent M none (n + 2) z 1 (s / 8) →
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (originCube d (m : ℤ)) u h g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        MemFractionalOn (cube d (m : ℤ)) s h.grad →
        let k : ℤ := (n : ℤ) - 2
        let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
        let Q := originCube d k
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        ∃ g0 : Vec d → Vec d,
          ∃ u0 h0 : H1Function (openCubeSet Q),
          ∃ v : DirichletForcedCubeSolution Q
              (aCutoffFamily M L (translatePotentialSample c omega))
              (fun y ↦ -g0 y),
            (∀ y, g0 y = g (y + c)) ∧
            Ch03.ABK26.MemCubeEuclideanFullWsp Q sOrder
              FiniteLpExponent.two (fun y ↦ g (y + c)) ∧
            (∀ y, u0.grad y = u.grad (y + c)) ∧
            IsForcedEquation Q
              (aCutoffFamily M L (translatePotentialSample c omega)) u0
              (fun y ↦ -(cubeFluctuationVec Q g0 y)) ∧
            v.boundaryData = h0 ∧
            (∀ y, h0.grad y = h.grad (y + c)) ∧
            ∀ H Ag U G L2 : ℝ,
              cubeAverage Q (coefficientEnergyDensity
                  (publicCoeffField Q
                    (aCutoffFamily M L (translatePotentialSample c omega)))
                  v.toH1.grad) ≤ H →
              sigma⁻¹ *
                    (1 + Section6Localization.subunitCollapseConstant d *
                      Section6Localization.subunitEnvelope (s / 8) (n + 2) *
                      Section6Localization.subunitDeviation M (n + 2)
                        (translatePotentialSample z omega)) *
                    (Fintype.card (Fin d) : ℝ) *
                  scaleNormalizedPositiveBesovVectorSeminormTwo Q (s / 3) g0 ^ 2 ≤ Ag →
              ForceBesovRegularity Q (s / 3)
                (fun y ↦ -(cubeFluctuationVec Q g0 y)) →
              cubeLpNorm Q 2
                  (fun y ↦ u0.toFun y - v.toH1.toFun y) ≤ U →
              scaleNormalizedPositiveBesovVectorSeminormTwo Q (s / 3)
                  (fun y ↦ -(cubeFluctuationVec Q g0 y)) ≤ G →
              boundaryNormalizedEuclideanL2 Q
                  (fun y ↦ -(cubeFluctuationVec Q g0 y)) ≤ L2 →
              normalizedSetAverage
                  (truncatedCube d (m : ℤ) (k - 2) q) (fun y ↦
                    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y *
                      vecNormSq (u.grad y)) ≤
                ((81 : ℝ) ^ d * (18 : ℝ) ^ d) *
                  (((61 / 8 : ℝ) + 4 * (64 * C ^ 4 * B)⁻¹) * H +
                      3 * Ag +
                      4 * projectedPhysicalGapBudgetCap
                        d Q s sigma B C U G L2) *
                    boundaryThreeQuarterRadiusIterationConst := by
  obtain ⟨C, B, hC, hB, hcell⟩ :=
    exists_projectedBoundaryCellPhysicalEnergy_of_budgetCaps d
  refine ⟨C, B, hC, hB, ?_⟩
  intro M s hs sOrder hsOrder L m n hmL hnm z x q omega hx hq hgood
    u h g hdir hg hh
  obtain ⟨g0, u0, h0, v, hg0, hgLocal, hu0, heq, hv, hh0, hraw⟩ :=
    hcell M s hs sOrder hsOrder L m n hmL hnm z x q omega hx hq hgood
      u h g hdir hg hh
  let k : ℤ := (n : ℤ) - 2
  let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
  let Q := originCube d k
  let sigma := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  refine ⟨g0, u0, h0, v, hg0, hgLocal, hu0, heq, hv, hh0, ?_⟩
  intro H Ag U G L2 hBE hAg hreg hU hG hL2
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hX : boundaryCommonGapPowerBudget Q s sigma B C 0
        (fun y ↦ u0.toFun y - v.toH1.toFun y)
        (fun y ↦ -(cubeFluctuationVec Q g0 y)) ≤
      projectedPhysicalGapBudgetCap d Q s sigma B C U G L2 :=
    boundaryCommonGapPowerBudget_zero_le_projectedPhysicalGapBudgetCap
      d Q (fun y ↦ u0.toFun y - v.toH1.toFun y)
        (fun y ↦ -(cubeFluctuationVec Q g0 y))
      hs0 hsigma hB hC hreg hU hG hL2
  exact hraw H Ag (projectedPhysicalGapBudgetCap d Q s sigma B C U G L2)
    hBE hAg hX

/-- Insert the sharp flat-comparator parent estimate into the physical
common-gap cap.  This is the first theorem in the boundary assembly where
the weighted root-energy feedback is visible in the literal consumer:
`Usharp` contains `R S Dforce Q g0`, and no smallness or absorption premise
is silently added. -/
theorem exists_boundaryCommonGapPowerBudget_le_projectedSharpParentCap
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ Cmean : ℝ, ∃ Cerror : ℝ≥0∞,
      0 ≤ Cmean ∧ Cerror < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L m n : ℕ) (hnL : n + 2 ≤ L)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (q z : Vec d)
        (hcontain :
          let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) ((n : ℤ) - 2)
          translateSet (c - z) (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
            cubeSet (originCube d ((n : ℤ) + 2)))
        (hgood : omega ∈ goodEvent M none (n + 2) z 1 (s / 8)),
      let k : ℤ := (n : ℤ) - 2
      let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
      let Q := originCube d k
      let A := aCutoffFamily M L (translatePotentialSample c omega)
      let sigma := tailAverage M L (n + 2) omega
        (translatedCube d ((n : ℤ) + 2) z)
      let s1 : FractionalOrder :=
        ⟨s / 3, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let smid : FractionalOrder :=
        ⟨s / 2, by
          have hs0 : 0 < s :=
            (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
          positivity,
          by linarith [hs.2]⟩
      let s2 : FractionalOrder :=
        ⟨s, by
          exact (mul_pos (by norm_num)
            (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
          by linarith [hs.2]⟩
      let E := Real.sqrt (192 * (d : ℝ)) *
        ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
          section6HomogenizationError M (s / 8) L (n + 2) omega z)
      let R := flatComparatorSharpGoodEventLoopBound Cerror d n sigma
        smid s1 s2 E
      ∀ {U : Set (Vec d)} {Dgeom S Dforce : ℝ} {gv : Vec d → Vec d}
        (g0 : Vec d → Vec d)
        (v : DirichletForcedCubeSolution Q A gv)
        (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (u0 h0 : H1Function (openCubeSet Q))
        (i : Fin d) (sg : ℝ),
        k < (m : ℤ) → (sg = 1 ∨ sg = -1) →
        Section6ExcessDecay.wellPlacedHalfGap (m : ℤ) k < sg * q i →
        MemH10 (openCubeSet (originCube d (m : ℤ)))
          (fun y ↦ u.toFun y - h.toFun y) →
        v.boundaryData = h0 →
        (∀ x, u0.toFun x = u.toFun (x + c)) →
        (∀ x, h0.toFun x = h.toFun (x + c)) →
        (∀ x, h0.grad x = h.grad (x + c)) →
        translatedCube d k c ⊆ U →
        U ⊆ openCubeSet (originCube d (m : ℤ)) →
        MeasurableSet U → 0 < volume U → volume U ≠ ⊤ →
        0 < (volume (translatedCube d k c)).toReal →
        0 < s →
        (∀ x ∈ U, ∀ y ∈ U, euclideanNorm (x - y) ≤ Dgeom) →
        fractionalSeminormOn U s h.grad ≠ ⊤ →
        Ch03.ABK26.MemCubeEuclideanFullWsp Q s2 FiniteLpExponent.two g0 →
        Ch03.ABK26.IsForcedEquation Q (A.coeffOn Q) u0 g0 →
        Ch03.ABK26.weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
          (A.coeffOn Q) u0 s1 smid FiniteLpExponent.two ≤ ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2
          FiniteLpExponent.two g0 ≤ ENNReal.ofReal Dforce →
        ∀ (K Cgap G L2 : ℝ),
          0 < K → 0 < Cgap →
          ForceBesovRegularity Q (s / 3)
            (fun y ↦ -(cubeFluctuationVec Q g0 y)) →
          scaleNormalizedPositiveBesovVectorSeminormTwo Q (s / 3)
              (fun y ↦ -(cubeFluctuationVec Q g0 y)) ≤ G →
          boundaryNormalizedEuclideanL2 Q
              (fun y ↦ -(cubeFluctuationVec Q g0 y)) ≤ L2 →
          let Usharp :=
            2 * Real.sqrt ((volume U).toReal /
                (volume (translatedCube d k c)).toReal) *
                normalizedL2On U (fun y ↦ u.toFun y - averageOn U u.toFun) +
              unitMeanZeroPoincareConst d * (3 : ℝ) ^ k * (d : ℝ) *
                Real.sqrt ((volume U).toReal /
                  (volume (translatedCube d k c)).toReal) *
                (Dgeom ^ (s + (d : ℝ) / 2) * s ^ (-(1 / 2 : ℝ)) *
                    (volume U).toReal ^ (-(1 / 2 : ℝ)) *
                      (fractionalSeminormOn U s h.grad).toReal +
                  euclideanNorm (averageVecOn U h.grad)) +
              (1 + 2 * Cmean) *
                (R S Dforce Q g0 + flatComparatorPriceConst d * (3 : ℝ) ^ k *
                  ∑ j : Fin d, normalizedL2On (translatedCube d k c)
                    (fun y ↦ h.grad y j)) +
              Cmean *
                (normalizedL2On (translatedCube d k c)
                    (fun y ↦ u.toFun y - volumeAverage
                      (translatedCube d k c) u.toFun) +
                  normalizedL2On (translatedCube d k c)
                    (fun y ↦ h.toFun y - volumeAverage
                      (translatedCube d k c) h.toFun)) +
              cubeLpNorm Q 2 (fun y ↦ v.toH1.toFun y - h0.toFun y)
          boundaryCommonGapPowerBudget Q s sigma K Cgap 0
              (fun y ↦ u0.toFun y - v.toH1.toFun y)
              (fun y ↦ -(cubeFluctuationVec Q g0 y)) ≤
            projectedPhysicalGapBudgetCap d Q s sigma K Cgap Usharp G L2 := by
  obtain ⟨Cmean, hCmean, hparent⟩ :=
    exists_cubeLpNorm_projected_sub_dirichletSolution_le_of_flatResidue d
  obtain ⟨Cerror, hCerror, hloop⟩ :=
    exists_normalizedL2On_sub_wellPlacedFlatComparator_le_goodEventLoop_of_forced_sharp
      d hd
  refine ⟨Cmean, Cerror, hCmean, hCerror, ?_⟩
  intro M s hs L m n hnL omega q z hcontain hgood
  dsimp only
  intro U Dgeom S Dforce gv g0 v u h u0 h0 i sg hkm hsg hface htrace hv
    hu0 hh0 hh0grad hPsub hUsub hUmeas hU0 hUtop hPpos hs0 hdiam hfrac
    hg0 heq hS hD K Cgap G L2 hK hCgap hreg hG hL2
  let Usharp :=
    2 * Real.sqrt ((volume U).toReal /
        (volume (translatedCube d ((n : ℤ) - 2)
          (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) ((n : ℤ) - 2)))).toReal) *
        normalizedL2On U (fun y ↦ u.toFun y - averageOn U u.toFun) +
      unitMeanZeroPoincareConst d * (3 : ℝ) ^ ((n : ℤ) - 2) * (d : ℝ) *
        Real.sqrt ((volume U).toReal /
          (volume (translatedCube d ((n : ℤ) - 2)
            (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) ((n : ℤ) - 2)))).toReal) *
        (Dgeom ^ (s + (d : ℝ) / 2) * s ^ (-(1 / 2 : ℝ)) *
            (volume U).toReal ^ (-(1 / 2 : ℝ)) *
              (fractionalSeminormOn U s h.grad).toReal +
          euclideanNorm (averageVecOn U h.grad)) +
      (1 + 2 * Cmean) *
        (flatComparatorSharpGoodEventLoopBound Cerror d n
            (tailAverage M L (n + 2) omega (translatedCube d ((n : ℤ) + 2) z))
            ⟨s / 2, by positivity, by linarith [hs.2]⟩
            ⟨s / 3, by positivity, by linarith [hs.2]⟩
            ⟨s, hs0, by linarith [hs.2]⟩
            (Real.sqrt (192 * (d : ℝ)) *
              ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
                section6HomogenizationError M (s / 8) L (n + 2) omega z))
            S Dforce (originCube d ((n : ℤ) - 2)) g0 +
          flatComparatorPriceConst d * (3 : ℝ) ^ ((n : ℤ) - 2) *
            ∑ j : Fin d, normalizedL2On
              (translatedCube d ((n : ℤ) - 2)
                (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) ((n : ℤ) - 2)))
              (fun y ↦ h.grad y j)) +
      Cmean *
        (normalizedL2On
            (translatedCube d ((n : ℤ) - 2)
              (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) ((n : ℤ) - 2)))
            (fun y ↦ u.toFun y - volumeAverage
              (translatedCube d ((n : ℤ) - 2)
                (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) ((n : ℤ) - 2)))
              u.toFun) +
          normalizedL2On
            (translatedCube d ((n : ℤ) - 2)
              (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) ((n : ℤ) - 2)))
            (fun y ↦ h.toFun y - volumeAverage
              (translatedCube d ((n : ℤ) - 2)
                (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) ((n : ℤ) - 2)))
              h.toFun)) +
      cubeLpNorm (originCube d ((n : ℤ) - 2)) 2
        (fun y ↦ v.toH1.toFun y - h0.toFun y)
  have hUsharp : cubeLpNorm (originCube d ((n : ℤ) - 2)) 2
        (fun y ↦ u0.toFun y - v.toH1.toFun y) ≤ Usharp := by
    apply hparent v u h u0 h0 i sg hkm hsg hface htrace hv hu0 hh0
      hh0grad hPsub hUsub hUmeas hU0 hUtop hPpos hs0 hdiam hfrac
    intro ubar hubarHarm hubarTrace
    simpa only [Usharp] using
      hloop M s hs L m n hnL omega q z hcontain hgood (by omega) g0 hg0
        u0 heq u.toFun ubar hubarHarm hubarTrace hu0 S Dforce hS hD
  have hsigma : 0 < tailAverage M L (n + 2) omega
      (translatedCube d ((n : ℤ) + 2) z) := by
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  simpa only [Usharp] using
    boundaryCommonGapPowerBudget_zero_le_projectedPhysicalGapBudgetCap
      d (originCube d ((n : ℤ) - 2))
      (fun y ↦ u0.toFun y - v.toH1.toFun y)
      (fun y ↦ -(cubeFluctuationVec (originCube d ((n : ℤ) - 2)) g0 y))
      hs0 hsigma hK hCgap hreg hUsharp hG hL2

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
