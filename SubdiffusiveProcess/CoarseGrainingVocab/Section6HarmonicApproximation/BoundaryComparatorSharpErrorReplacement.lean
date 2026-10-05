module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryComparatorErrorReplacement
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorSharpErrorLoop

@[expose] public section

/-! # Sharp replacement of the physical flat-comparator residue -/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open scoped ENNReal BigOperators

noncomputable section

/-- Good-event boundary parent estimate with the sharp additive-dual
comparator loop inserted. -/
theorem exists_cubeLpNorm_projected_sub_dirichletSolution_le_goodEventComparatorPrices_sharp
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ Cmean : ℝ, ∃ Cerror : ℝ≥0∞,
      0 ≤ Cmean ∧ Cerror < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L m n : ℕ) (_hnL : n + 2 ≤ L)
        (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (q z : Vec d)
        (_hcontain :
          let c := wellPlacedCentre q (m : ℤ) ((n : ℤ) - 2)
          translateSet (c - z) (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
            cubeSet (originCube d ((n : ℤ) + 2)))
        (_hgood : omega ∈ goodEvent M none (n + 2) z 1 (s / 8)),
      let k : ℤ := (n : ℤ) - 2
      let c := wellPlacedCentre q (m : ℤ) k
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
      ∀ {U : Set (Vec d)} {Dgeom S Dforce : ℝ}
        (g0 : Vec d → Vec d)
        (v : DirichletForcedCubeSolution Q A g0)
        (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (u0 h0 : H1Function (openCubeSet Q))
        (i : Fin d) (sg : ℝ),
        k < (m : ℤ) → (sg = 1 ∨ sg = -1) →
        wellPlacedHalfGap (m : ℤ) k < sg * q i →
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
        cubeLpNorm Q 2 (fun y ↦ u0.toFun y - v.toH1.toFun y) ≤
          2 * Real.sqrt ((volume U).toReal / (volume (translatedCube d k c)).toReal) *
              normalizedL2On U (fun y ↦ u.toFun y - averageOn U u.toFun) +
            unitMeanZeroPoincareConst d * (3 : ℝ) ^ k * (d : ℝ) *
              Real.sqrt ((volume U).toReal / (volume (translatedCube d k c)).toReal) *
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
                  (fun y ↦ u.toFun y - volumeAverage (translatedCube d k c) u.toFun) +
                normalizedL2On (translatedCube d k c)
                  (fun y ↦ h.toFun y - volumeAverage (translatedCube d k c) h.toFun)) +
            cubeLpNorm Q 2 (fun y ↦ v.toH1.toFun y - h0.toFun y) := by
  obtain ⟨Cmean, hCmean, hparent⟩ :=
    exists_cubeLpNorm_projected_sub_dirichletSolution_le_of_flatResidue d
  obtain ⟨Cerror, hCerror, hloop⟩ :=
    exists_normalizedL2On_sub_wellPlacedFlatComparator_le_goodEventLoop_of_forced_sharp
      d hd
  refine ⟨Cmean, Cerror, hCmean, hCerror, ?_⟩
  intro M s hs L m n hnL omega q z hcontain hgood
  dsimp only
  intro U Dgeom S Dforce g0 v u h u0 h0 i sg hkm hsg hover htrace hv
    hu0 hh0 hh0grad hPsub hUsub hUmeas hU0 hUtop hPpos hs0 hdiam hfrac
    hg0 hu0eq hS hD
  apply hparent v u h u0 h0 i sg hkm hsg hover htrace hv hu0 hh0 hh0grad
    hPsub hUsub hUmeas hU0 hUtop hPpos hs0 hdiam hfrac
  intro ubar hubarHarm hubarTrace
  exact hloop M s hs L m n hnL omega q z hcontain hgood (by omega) g0 hg0
    u0 hu0eq u.toFun ubar hubarHarm hubarTrace hu0 S Dforce hS hD

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
