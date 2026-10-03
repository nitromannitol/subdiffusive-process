module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorSharpErrorLoop
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffLocalError

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff

open Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open scoped ENNReal

noncomputable section

/-- Cutoff good-event specialization of the sharp local comparator estimate. -/
theorem exists_cubeLpNorm_sub_le_flatComparatorCutoffGoodEventBound_sharp
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L n : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (y z : Vec d)
        (_hcontain : translateSet (y - z)
          (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
            cubeSet (originCube d ((n : ℤ) + 2)))
        (_hgood : omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8)),
      let Q := originCube d ((n : ℤ) - 2)
      let A := aCutoffFamily M L (translatePotentialSample y omega)
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
      ∀ (g : Vec d → Vec d), MemCubeEuclideanFullWsp Q s2
          FiniteLpExponent.two g →
      ∀ u v : H1Function (openCubeSet Q),
        IsForcedEquation Q (A.coeffOn Q) u g →
        IsScalarForcedEquation Q sigma v g →
        HasH10Difference Q u v →
      ∀ S D : ℝ,
        weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
          (A.coeffOn Q) u s1 smid FiniteLpExponent.two ≤ ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2
          FiniteLpExponent.two g ≤ ENNReal.ofReal D →
        let E := Real.sqrt (192 * (d : ℝ)) *
          ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
            section6HomogenizationError M (s / 8) L (n + 2) omega z)
        cubeLpNorm Q 2 (fun x => u.toFun x - v.toFun x) ≤
          (flatComparatorSharpSpectralConstant d *
            ENNReal.ofReal (centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ *
              (flatComparatorLocalCoarseBound C sigma smid s1 s2 E E S D
                ((n : ℤ) - 3)).toReal)).toReal := by
  obtain ⟨C, hCtop, hmain⟩ :=
    exists_cubeLpNorm_sub_le_flatComparatorManuscriptBound_sharp d hd
  refine ⟨C, hCtop, ?_⟩
  intro M s hs L n omega y z hcontain hgood
  dsimp only
  intro g hg u v hu hv huv S D hS hD
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hs1 : s < 1 := lt_of_le_of_lt hs.2 (by norm_num)
  let E := Real.sqrt (192 * (d : ℝ)) *
    ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
      section6HomogenizationError M (s / 8) L (n + 2) omega z)
  have hE := localHomogenizationError_two_le_cutoffAnchor_of_closedContainment
    M hs L n omega y z hcontain hgood
  have hres := hmain ((n : ℤ) - 2) s hs0 hs1 hs.2
    (aCutoffFamily M L (translatePotentialSample y omega))
    (tailAverage M L (n + 2) omega (translatedCube d ((n : ℤ) + 2) z))
    (by
      rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
      rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
      exact tailCoefficientCubeAverage_pos M L (n + 2)
        (translatePotentialSample z omega)) g hg u v hu hv huv E S D
    (by simpa only [E] using hE)
    (by simpa [originCube] using hS) hD
  simpa only [E, show ((n : ℤ) - 2) - 1 = (n : ℤ) - 3 by ring] using hres

/-- Complete sharp local comparator loop at a finite cutoff, including the
direct forcing comparison to the unit harmonic function. -/
theorem exists_cubeLpNorm_sub_unitHarmonic_le_flatComparatorCutoffGoodEvent_sharp
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L n : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (y z : Vec d)
        (_hcontain : translateSet (y - z)
          (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
            cubeSet (originCube d ((n : ℤ) + 2)))
        (_hgood : omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8)),
      let Q := originCube d ((n : ℤ) - 2)
      let A := aCutoffFamily M L (translatePotentialSample y omega)
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
      ∀ (g : Vec d → Vec d), MemCubeEuclideanFullWsp Q s2
          FiniteLpExponent.two g →
      ∀ u v h : H1Function (openCubeSet Q),
        IsForcedEquation Q (A.coeffOn Q) u g →
        IsScalarForcedEquation Q sigma v g →
        HasH10Difference Q u v →
        IsUnitWeaklyHarmonicOn (openCubeSet Q) h →
        HasH10Difference Q u h →
      ∀ S D : ℝ,
        weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
          (A.coeffOn Q) u s1 smid FiniteLpExponent.two ≤ ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2
          FiniteLpExponent.two g ≤ ENNReal.ofReal D →
        let E := Real.sqrt (192 * (d : ℝ)) *
          ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
            section6HomogenizationError M (s / 8) L (n + 2) omega z)
        cubeLpNorm Q 2 (fun x ↦ u.toFun x - h.toFun x) ≤
          (flatComparatorSharpSpectralConstant d *
            ENNReal.ofReal (centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ *
              (flatComparatorLocalCoarseBound C sigma smid s1 s2 E E S D
                ((n : ℤ) - 3)).toReal)).toReal +
          unitDirichletPoincareConst d * (3 : ℝ) ^ ((n : ℤ) - 2) *
            (d : ℝ) * sigma⁻¹ *
              (Real.sqrt (Fintype.card (Fin d) : ℝ) *
                scaleNormalizedPositiveBesovVectorSeminormTwo Q smid.1 g) := by
  obtain ⟨C, hCtop, hcoarse⟩ :=
    exists_cubeLpNorm_sub_le_flatComparatorCutoffGoodEventBound_sharp d hd
  refine ⟨C, hCtop, ?_⟩
  intro M s hs L n omega y z hcontain hgood
  dsimp only
  intro g hg u v h hu hv huv hh huh S D hS hD
  let s1 : FractionalOrder := ⟨s / 3, by
    have hs0 : 0 < s :=
      (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
    positivity, by linarith [hs.2]⟩
  let smid : FractionalOrder := ⟨s / 2, by
    have hs0 : 0 < s :=
      (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
    positivity, by linarith [hs.2]⟩
  let s2 : FractionalOrder := ⟨s, by
    exact (mul_pos (by norm_num)
      (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1,
    by linarith [hs.2]⟩
  let E := Real.sqrt (192 * (d : ℝ)) *
    ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
      section6HomogenizationError M (s / 8) L (n + 2) omega z)
  have hcoarse' := hcoarse M s hs L n omega y z hcontain hgood
    g hg u v hu hv huv S D (by simpa [s1, smid] using hS) hD
  have hreg : ForceBesovRegularity (originCube d ((n : ℤ) - 2)) smid.1 g := by
    apply forceBesovRegularity_of_memCubeEuclideanFullWsp_lt hg
    have hs0 : 0 < s :=
      (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
    dsimp [smid, s2]
    linarith
  have hvh : HasH10Difference (originCube d ((n : ℤ) - 2)) v h :=
    hasH10Difference_trans (hasH10Difference_symm huv) huh
  have hsigma : 0 < tailAverage M L (n + 2) omega
      (translatedCube d ((n : ℤ) + 2) z) := by
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hforce := cubeLpNorm_scalarForced_sub_unitHarmonic_le_positiveBesov
    ((n : ℤ) - 2) hsigma hreg hv hh hvh
  exact cubeLpNorm_sub_unitHarmonic_le_add
    (originCube d ((n : ℤ) - 2)) u v h
    (by simpa only [E, s1, smid, s2] using hcoarse')
    (by simpa only [smid] using hforce)

/-- Arbitrary translated-cube physical-frame sharp loop at a finite cutoff. -/
theorem exists_normalizedL2On_sub_flatComparator_le_cutoffGoodEventLoop_of_forced_sharp
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L n : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (y z : Vec d)
        (_hcontain : translateSet (y - z)
          (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
            cubeSet (originCube d ((n : ℤ) + 2)))
        (_hgood : omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8)),
      let Q := originCube d ((n : ℤ) - 2)
      let A := aCutoffFamily M L (translatePotentialSample y omega)
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
      ∀ (g : Vec d → Vec d), MemCubeEuclideanFullWsp Q s2
          FiniteLpExponent.two g →
      ∀ u0 : H1Function (openCubeSet Q),
        IsForcedEquation Q (A.coeffOn Q) u0 g →
      ∀ (uPhysical : Vec d → ℝ)
        (ubar : H1Function (translateSet y (openCubeSet Q))),
        IsUnitWeaklyHarmonicOn (translateSet y (openCubeSet Q)) ubar →
        MemH10 (translateSet y (openCubeSet Q))
          (fun p ↦ ubar.toFun p - uPhysical p) →
        (∀ p, u0.toFun p = uPhysical (p + y)) →
      ∀ S D : ℝ,
        weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
          (A.coeffOn Q) u0 s1 smid FiniteLpExponent.two ≤ ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2
          FiniteLpExponent.two g ≤ ENNReal.ofReal D →
        let E := Real.sqrt (192 * (d : ℝ)) *
          ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
            section6HomogenizationError M (s / 8) L (n + 2) omega z)
        normalizedL2On (translateSet y (openCubeSet Q))
            (fun p ↦ uPhysical p - ubar.toFun p) ≤
          flatComparatorSharpGoodEventLoopBound C d n sigma smid s1 s2
            E S D Q g := by
  obtain ⟨C, hCtop, hloop⟩ :=
    exists_cubeLpNorm_sub_unitHarmonic_le_flatComparatorCutoffGoodEvent_sharp d hd
  refine ⟨C, hCtop, ?_⟩
  intro M s hs L n omega y z hcontain hgood
  dsimp only
  intro g hg u0 hu0 uPhysical ubar hh ht hu0Physical S D hS hD
  have hgTwo : MemLp g 2 (normalizedCubeMeasure (originCube d ((n : ℤ) - 2))) :=
    MemCubeEuclideanFullWsp.memLpTwo (by norm_num) hg
  have hgCube : MemVectorL2 (cubeSet (originCube d ((n : ℤ) - 2))) g :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure
      (originCube d ((n : ℤ) - 2)) hgTwo
  have hgOpen : MemVectorL2 (openCubeSet (originCube d ((n : ℤ) - 2))) g := by
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using hgCube
  have hsigma : 0 < tailAverage M L (n + 2) omega
      (translatedCube d ((n : ℤ) + 2) z) := by
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  let v0 := sourceForcedReplacement
    (scalarConstantCoeffMatrix (d := d) hsigma) u0 hgOpen
  have hv0 : IsScalarForcedEquation (originCube d ((n : ℤ) - 2))
      (tailAverage M L (n + 2) omega (translatedCube d ((n : ℤ) + 2) z)) v0 g :=
    isScalarForcedEquation_sourceForcedReplacement hsigma u0 hgOpen
  have huv0 : HasH10Difference (originCube d ((n : ℤ) - 2)) u0 v0 :=
    hasH10Difference_sourceForcedReplacement
      (scalarConstantCoeffMatrix (d := d) hsigma) u0 hgOpen
  obtain ⟨ubar0, hh0, hu0bar0, hnorm⟩ :=
    exists_recenteredFlatComparator (originCube d ((n : ℤ) - 2)) y
      u0 uPhysical ubar hh ht hu0Physical
  rw [hnorm]
  have hout := hloop M s hs L n omega y z hcontain hgood g hg u0 v0 ubar0
    hu0 hv0 huv0 hh0 hu0bar0 S D hS hD
  simpa only [flatComparatorSharpGoodEventLoopBound] using hout

/-- The cutoff sharp loop at the `[NeZero d]` signature of the Section 6
anchors. -/
theorem exists_normalizedL2On_sub_flatComparator_le_cutoffGoodEventLoop_of_forced_sharp_neZero
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L n : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (y z : Vec d)
        (_hcontain : translateSet (y - z)
          (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
            cubeSet (originCube d ((n : ℤ) + 2)))
        (_hgood : omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8)),
      let Q := originCube d ((n : ℤ) - 2)
      let A := aCutoffFamily M L (translatePotentialSample y omega)
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
      ∀ (g : Vec d → Vec d), MemCubeEuclideanFullWsp Q s2
          FiniteLpExponent.two g →
      ∀ u0 : H1Function (openCubeSet Q),
        IsForcedEquation Q (A.coeffOn Q) u0 g →
      ∀ (uPhysical : Vec d → ℝ)
        (ubar : H1Function (translateSet y (openCubeSet Q))),
        IsUnitWeaklyHarmonicOn (translateSet y (openCubeSet Q)) ubar →
        MemH10 (translateSet y (openCubeSet Q))
          (fun p ↦ ubar.toFun p - uPhysical p) →
        (∀ p, u0.toFun p = uPhysical (p + y)) →
      ∀ S D : ℝ,
        weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
          (A.coeffOn Q) u0 s1 smid FiniteLpExponent.two ≤ ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2
          FiniteLpExponent.two g ≤ ENNReal.ofReal D →
        let E := Real.sqrt (192 * (d : ℝ)) *
          ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
            section6HomogenizationError M (s / 8) L (n + 2) omega z)
        normalizedL2On (translateSet y (openCubeSet Q))
            (fun p ↦ uPhysical p - ubar.toFun p) ≤
          flatComparatorSharpGoodEventLoopBound C d n sigma smid s1 s2
            E S D Q g := by
  classical
  by_cases hmodel : Nonempty (SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
  · let M0 : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d := Classical.choice hmodel
    exact exists_normalizedL2On_sub_flatComparator_le_cutoffGoodEventLoop_of_forced_sharp
      d M0.shellPrefix.dimension
  · refine ⟨0, ENNReal.zero_lt_top, ?_⟩
    intro M
    exact (hmodel ⟨M⟩).elim

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff
