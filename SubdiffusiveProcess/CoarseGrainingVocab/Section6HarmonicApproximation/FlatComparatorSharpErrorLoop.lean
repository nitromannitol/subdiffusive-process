module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorSharpReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorTransport
public import Homogenization.Book.Ch03.ABK26.FinitePToLegacyQTwo

@[expose] public section

/-!
# Sharp flat-comparator error loop

This is the manuscript-corridor specialization of the existing comparator
loop, using the additive-dual readout from `FlatComparatorSharpReadout`.
Its constant is dimension-only and therefore preserves the printed power of
the fractional order.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Good-event specialization of the sharp local comparator estimate. -/
theorem exists_cubeLpNorm_sub_le_flatComparatorGoodEventBound_sharp
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L n : ℕ) (_hnL : n + 2 ≤ L)
        (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (y z : Vec d)
        (_hcontain : translateSet (y - z)
          (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
            cubeSet (originCube d ((n : ℤ) + 2)))
        (_hgood : omega ∈ goodEvent M none (n + 2) z 1 (s / 8)),
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
  intro M s hs L n hnL omega y z hcontain hgood
  dsimp only
  intro g hg u v hu hv huv S D hS hD
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hs1 : s < 1 := lt_of_le_of_lt hs.2 (by norm_num)
  let E := Real.sqrt (192 * (d : ℝ)) *
    ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
      section6HomogenizationError M (s / 8) L (n + 2) omega z)
  have hE := localHomogenizationError_two_le_anchor_of_closedContainment
    M hs L n hnL omega y z hcontain hgood
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

/-- Complete sharp local comparator loop, including the direct forcing
comparison to the unit harmonic function. -/
theorem exists_cubeLpNorm_sub_unitHarmonic_le_flatComparatorGoodEvent_sharp
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L n : ℕ) (_hnL : n + 2 ≤ L)
        (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (y z : Vec d)
        (_hcontain : translateSet (y - z)
          (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
            cubeSet (originCube d ((n : ℤ) + 2)))
        (_hgood : omega ∈ goodEvent M none (n + 2) z 1 (s / 8)),
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
    exists_cubeLpNorm_sub_le_flatComparatorGoodEventBound_sharp d hd
  refine ⟨C, hCtop, ?_⟩
  intro M s hs L n hnL omega y z hcontain hgood
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
  have hcoarse' := hcoarse M s hs L n hnL omega y z hcontain hgood
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

/-- Scalar carrier of the sharp good-event comparator loop. -/
noncomputable def flatComparatorSharpGoodEventLoopBound
    (C : ℝ≥0∞) (d : ℕ) [NeZero d] (n : ℕ) (sigma : ℝ)
    (smid s1 s2 : FractionalOrder) (E S D : ℝ)
    (Q : TriadicCube d) (g : Vec d → Vec d) : ℝ :=
  (flatComparatorSharpSpectralConstant d *
      ENNReal.ofReal (centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ *
        (flatComparatorLocalCoarseBound C sigma smid s1 s2 E E S D
          ((n : ℤ) - 3)).toReal)).toReal +
    unitDirichletPoincareConst d * (3 : ℝ) ^ ((n : ℤ) - 2) *
      (d : ℝ) * sigma⁻¹ *
        (Real.sqrt (Fintype.card (Fin d) : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q smid.1 g)

/-- Real-valued readout of the sharp loop.  Compared with the older carrier,
the spectral factor contributes no additional `smid⁻¹/²`. -/
theorem flatComparatorSharpGoodEventLoopBound_le_realReadout
    (C : ℝ≥0∞) (d n : ℕ) [NeZero d] (sigma : ℝ)
    (smid s1 s2 : FractionalOrder) (E S D : ℝ)
    (Q : TriadicCube d) (g : Vec d → Vec d)
    (hmid2 : smid.1 < s2.1) (hsigma : 0 < sigma)
    (hE : 0 ≤ E) (hS : 0 ≤ S) (hD : 0 ≤ D) :
    flatComparatorSharpGoodEventLoopBound C d n sigma smid s1 s2 E S D Q g ≤
      (flatComparatorSharpSpectralConstant d).toReal *
        centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ *
          (Real.rpow smid.1 (-(1 / 2 : ℝ)) *
            (C.toReal * smid.1⁻¹ * Real.sqrt sigma *
                Real.rpow 3 s1.1 * E * S +
              C.toReal * Real.rpow smid.1 (-(9 / 2 : ℝ)) *
                (s2.1 - smid.1)⁻¹ *
                (1 + (Real.rpow 3 (s1.1 / 2) * E) ^ 2) *
                Real.rpow 3 (s2.1 * (((n : ℤ) - 3 : ℤ) : ℝ)) * D)) +
        unitDirichletPoincareConst d * (3 : ℝ) ^ ((n : ℤ) - 2) *
          (d : ℝ) * sigma⁻¹ *
            (Real.sqrt (Fintype.card (Fin d) : ℝ) *
              scaleNormalizedPositiveBesovVectorSeminormTwo Q smid.1 g) := by
  have hbudget := flatComparatorLocalCoarseBound_toReal_le
    C sigma smid s1 s2 E E S D ((n : ℤ) - 3)
      hmid2 hsigma hE hE hS hD
  have hscale : 0 ≤ centeredCubeScale ((n : ℤ) - 2) :=
    (centeredCubeScale_pos ((n : ℤ) - 2)).le
  have hinv : 0 ≤ sigma⁻¹ := inv_nonneg.mpr hsigma.le
  have hreal0 : 0 ≤ centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ *
      (flatComparatorLocalCoarseBound C sigma smid s1 s2 E E S D
        ((n : ℤ) - 3)).toReal := by positivity
  unfold flatComparatorSharpGoodEventLoopBound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hreal0]
  let R : ℝ := Real.rpow smid.1 (-(1 / 2 : ℝ)) *
    (C.toReal * smid.1⁻¹ * Real.sqrt sigma * Real.rpow 3 s1.1 * E * S +
      C.toReal * Real.rpow smid.1 (-(9 / 2 : ℝ)) *
        (s2.1 - smid.1)⁻¹ *
        (1 + (Real.rpow 3 (s1.1 / 2) * E) ^ 2) *
        Real.rpow 3 (s2.1 * (((n : ℤ) - 3 : ℤ) : ℝ)) * D)
  have hfirst :
      (flatComparatorSharpSpectralConstant d).toReal *
          (centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ *
            (flatComparatorLocalCoarseBound C sigma smid s1 s2 E E S D
              ((n : ℤ) - 3)).toReal) ≤
        (flatComparatorSharpSpectralConstant d).toReal *
          centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ * R := by
    calc
      _ ≤ (flatComparatorSharpSpectralConstant d).toReal *
          (centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ * R) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (by simpa only [R] using hbudget)
            (mul_nonneg hscale hinv)) ENNReal.toReal_nonneg
      _ = _ := by ring
  simpa only [R] using add_le_add hfirst (le_refl
    (unitDirichletPoincareConst d * (3 : ℝ) ^ ((n : ℤ) - 2) *
      (d : ℝ) * sigma⁻¹ *
        (Real.sqrt (Fintype.card (Fin d) : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q smid.1 g)))

/-- Arbitrary translated-cube physical-frame sharp loop.  This is the
post-energy interface used by harmonic approximation; unlike the projected
boundary-cell wrapper below, its centre is the literal `y` from the
statement. -/
theorem exists_normalizedL2On_sub_flatComparator_le_goodEventLoop_of_forced_sharp
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L n : ℕ) (_hnL : n + 2 ≤ L)
        (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (y z : Vec d)
        (_hcontain : translateSet (y - z)
          (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
            cubeSet (originCube d ((n : ℤ) + 2)))
        (_hgood : omega ∈ goodEvent M none (n + 2) z 1 (s / 8)),
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
    exists_cubeLpNorm_sub_unitHarmonic_le_flatComparatorGoodEvent_sharp d hd
  refine ⟨C, hCtop, ?_⟩
  intro M s hs L n hnL omega y z hcontain hgood
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
  have hout := hloop M s hs L n hnL omega y z hcontain hgood g hg u0 v0 ubar0
    hu0 hv0 huv0 hh0 hu0bar0 S D hS hD
  simpa only [flatComparatorSharpGoodEventLoopBound] using hout

/-- Literal well-placed physical-frame sharp loop, with the scalar forced
replacement constructed internally. -/
theorem exists_normalizedL2On_sub_wellPlacedFlatComparator_le_goodEventLoop_of_forced_sharp
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L m n : ℕ) (_hnL : n + 2 ≤ L)
        (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (q z : Vec d)
        (_hcontain :
          let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) ((n : ℤ) - 2)
          translateSet (c - z) (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
            cubeSet (originCube d ((n : ℤ) + 2)))
        (_hgood : omega ∈ goodEvent M none (n + 2) z 1 (s / 8)),
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
      ∀ (_hkm : k ≤ (m : ℤ)) (g : Vec d → Vec d),
        MemCubeEuclideanFullWsp Q s2 FiniteLpExponent.two g →
      ∀ u0 : H1Function (openCubeSet Q),
        IsForcedEquation Q (A.coeffOn Q) u0 g →
      ∀ (uPhysical : Vec d → ℝ)
        (ubar : H1Function (truncatedWindow c (m : ℤ) k)),
        IsUnitWeaklyHarmonicOn (truncatedWindow c (m : ℤ) k) ubar →
        MemH10 (truncatedWindow c (m : ℤ) k)
          (fun y ↦ ubar.toFun y - uPhysical y) →
        (∀ x, u0.toFun x = uPhysical (x + c)) →
      ∀ S D : ℝ,
        weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
          (A.coeffOn Q) u0 s1 smid FiniteLpExponent.two ≤ ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2
          FiniteLpExponent.two g ≤ ENNReal.ofReal D →
        let E := Real.sqrt (192 * (d : ℝ)) *
          ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
            section6HomogenizationError M (s / 8) L (n + 2) omega z)
        normalizedL2On (translatedCube d k c)
            (fun y ↦ uPhysical y - ubar.toFun y) ≤
          flatComparatorSharpGoodEventLoopBound C d n sigma smid s1 s2 E S D Q g := by
  obtain ⟨C, hCtop, hloop⟩ :=
    exists_cubeLpNorm_sub_unitHarmonic_le_flatComparatorGoodEvent_sharp d hd
  refine ⟨C, hCtop, ?_⟩
  intro M s hs L m n hnL omega q z hcontain hgood
  dsimp only
  intro hkm g hg u0 hu0 uPhysical ubar hh ht hu0Physical S D hS hD
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
    exists_recenteredFlatComparator_wellPlaced hkm q u0 uPhysical ubar
      hh ht hu0Physical
  rw [hnorm]
  have hout := hloop M s hs L n hnL omega
    (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) ((n : ℤ) - 2)) z
    hcontain hgood g hg u0 v0 ubar0 hu0 hv0 huv0 hh0 hu0bar0 S D hS hD
  simpa only [flatComparatorSharpGoodEventLoopBound] using hout

/-- The sharp physical-frame loop at the model-facing dimension signature.

The Chapter 3 endpoint is stated with `2 ≤ d`, while the Section 6 anchors
quantify under `[NeZero d]` and introduce the model only after the dimensional
constant.  A model itself contains the stronger witness
`M.shellPrefix.dimension : 2 ≤ d`.  Splitting on whether the model type is
inhabited lets us select that witness before choosing the constant; in the
empty branch the universally quantified model conclusion is vacuous.  Thus
no analytic dimension restriction is added to the consumer. -/
theorem exists_normalizedL2On_sub_wellPlacedFlatComparator_le_goodEventLoop_of_forced_sharp_neZero
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L m n : ℕ) (_hnL : n + 2 ≤ L)
        (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (q z : Vec d)
        (_hcontain :
          let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) ((n : ℤ) - 2)
          translateSet (c - z) (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
            cubeSet (originCube d ((n : ℤ) + 2)))
        (_hgood : omega ∈ goodEvent M none (n + 2) z 1 (s / 8)),
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
      ∀ (_hkm : k ≤ (m : ℤ)) (g : Vec d → Vec d),
        MemCubeEuclideanFullWsp Q s2 FiniteLpExponent.two g →
      ∀ u0 : H1Function (openCubeSet Q),
        IsForcedEquation Q (A.coeffOn Q) u0 g →
      ∀ (uPhysical : Vec d → ℝ)
        (ubar : H1Function (truncatedWindow c (m : ℤ) k)),
        IsUnitWeaklyHarmonicOn (truncatedWindow c (m : ℤ) k) ubar →
        MemH10 (truncatedWindow c (m : ℤ) k)
          (fun y ↦ ubar.toFun y - uPhysical y) →
        (∀ x, u0.toFun x = uPhysical (x + c)) →
      ∀ S D : ℝ,
        weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
          (A.coeffOn Q) u0 s1 smid FiniteLpExponent.two ≤ ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2
          FiniteLpExponent.two g ≤ ENNReal.ofReal D →
        let E := Real.sqrt (192 * (d : ℝ)) *
          ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) *
            section6HomogenizationError M (s / 8) L (n + 2) omega z)
        normalizedL2On (translatedCube d k c)
            (fun y ↦ uPhysical y - ubar.toFun y) ≤
          flatComparatorSharpGoodEventLoopBound C d n sigma smid s1 s2 E S D Q g := by
  classical
  by_cases hmodel : Nonempty (_root_.SubdiffusiveProcess.Model.GMCModel d)
  · let M0 : _root_.SubdiffusiveProcess.Model.GMCModel d := Classical.choice hmodel
    exact
      exists_normalizedL2On_sub_wellPlacedFlatComparator_le_goodEventLoop_of_forced_sharp
        d M0.shellPrefix.dimension
  · refine ⟨0, ENNReal.zero_lt_top, ?_⟩
    intro M
    exact (hmodel ⟨M⟩).elim

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
