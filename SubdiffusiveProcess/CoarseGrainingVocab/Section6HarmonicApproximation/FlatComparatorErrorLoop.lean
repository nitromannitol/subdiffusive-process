module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorGoodEvent
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorTransport
public import Homogenization.Book.Ch03.ABK26.FinitePToLegacyQTwo

@[expose] public section

/-!
# The flat-comparator homogenization/forcing loop

This module combines the amplitude-one good-event coarse error with the
constant-coefficient forcing comparison.  Its output is the physical
coefficient solution minus the flat harmonic comparator with the same trace.


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

/-- Full finite-`p` Euclidean fractional membership is stable under
pointwise negation. -/
theorem memCubeEuclideanFullWsp_neg
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    {g : Vec d → Vec d} (hg : MemCubeEuclideanFullWsp Q s p g) :
    MemCubeEuclideanFullWsp Q s p (fun x ↦ -g x) := by
  constructor
  · simpa only [map_neg] using! hg.1.neg
  · unfold MemCubeEuclideanWsp
    have hkernel : cubeEuclideanWspKernel s p (fun x ↦ -g x) =
        fun z ↦ -cubeEuclideanWspKernel s p g z := by
      funext z
      rw [cubeEuclideanWspKernel_apply, cubeEuclideanWspKernel_apply]
      have hsub : -g z.1 - -g z.2 = -(g z.1 - g z.2) := by abel
      rw [hsub, show HilbertVec.ofVec (-(g z.1 - g z.2)) =
        -HilbertVec.ofVec (g z.1 - g z.2) by
          exact (HilbertVec.ofVecL d).map_neg _, smul_neg]
    rw [hkernel]
    exact hg.2.neg

/-- A strict lower order of a full Euclidean `W^{s,2}` datum supplies the
legacy positive-Besov regularity needed by the flat forcing estimate. -/
theorem forceBesovRegularity_of_memCubeEuclideanFullWsp_lt
    [NeZero d]
    {Q : TriadicCube d} {s t : FractionalOrder} {g : Vec d → Vec d}
    (hg : MemCubeEuclideanFullWsp Q s FiniteLpExponent.two g)
    (hts : t.1 < s.1) : ForceBesovRegularity Q t.1 g := by
  have hneg := memCubeEuclideanFullWsp_neg hg
  simpa only [neg_neg] using
    hneg.toCubeVectorBesovHRegularity_neg_of_lt (by norm_num) hts

/-- The complete local comparator loop.  The first summand is the established
finite-`p` homogenization readout; the second is the direct centered-force
price. -/
theorem exists_cubeLpNorm_sub_unitHarmonic_le_flatComparatorGoodEvent
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
          (Section6Dirichlet.dirichletSpectralReadoutConstant smid d *
            ENNReal.ofReal (centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ *
              (flatComparatorLocalCoarseBound C sigma smid s1 s2 E E S D
                ((n : ℤ) - 3)).toReal)).toReal +
          unitDirichletPoincareConst d * (3 : ℝ) ^ ((n : ℤ) - 2) *
            (d : ℝ) * sigma⁻¹ *
              (Real.sqrt (Fintype.card (Fin d) : ℝ) *
                scaleNormalizedPositiveBesovVectorSeminormTwo Q smid.1 g) := by
  obtain ⟨C, hCtop, hcoarse⟩ :=
    exists_cubeLpNorm_sub_le_flatComparatorGoodEventBound d hd
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



theorem exists_normalizedL2On_sub_flatComparator_le_goodEventLoop
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s : ℝ)
        (hs : s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ))
        (L n : ℕ) (_hnL : n + 2 ≤ L)
        (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (c z : Vec d)
        (_hcontain : translateSet (c - z)
          (cubeSet (originCube d ((n : ℤ) - 2))) ⊆
            cubeSet (originCube d ((n : ℤ) + 2)))
        (_hgood : omega ∈ goodEvent M none (n + 2) z 1 (s / 8)),
      let Q := originCube d ((n : ℤ) - 2)
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
      ∀ (g : Vec d → Vec d), MemCubeEuclideanFullWsp Q s2
          FiniteLpExponent.two g →
      ∀ u0 v0 : H1Function (openCubeSet Q),
        IsForcedEquation Q (A.coeffOn Q) u0 g →
        IsScalarForcedEquation Q sigma v0 g →
        HasH10Difference Q u0 v0 →
      ∀ (uPhysical : Vec d → ℝ)
        (ubar : H1Function (translateSet c (openCubeSet Q))),
        IsUnitWeaklyHarmonicOn (translateSet c (openCubeSet Q)) ubar →
        MemH10 (translateSet c (openCubeSet Q))
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
        normalizedL2On (translateSet c (openCubeSet Q))
            (fun y ↦ uPhysical y - ubar.toFun y) ≤
          (Section6Dirichlet.dirichletSpectralReadoutConstant smid d *
            ENNReal.ofReal (centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ *
              (flatComparatorLocalCoarseBound C sigma smid s1 s2 E E S D
                ((n : ℤ) - 3)).toReal)).toReal +
          unitDirichletPoincareConst d * (3 : ℝ) ^ ((n : ℤ) - 2) *
            (d : ℝ) * sigma⁻¹ *
              (Real.sqrt (Fintype.card (Fin d) : ℝ) *
                scaleNormalizedPositiveBesovVectorSeminormTwo Q smid.1 g) := by
  obtain ⟨C, hCtop, hloop⟩ :=
    exists_cubeLpNorm_sub_unitHarmonic_le_flatComparatorGoodEvent d hd
  refine ⟨C, hCtop, ?_⟩
  intro M s hs L n hnL omega c z hcontain hgood
  dsimp only
  intro g hg u0 v0 hu0 hv0 huv0 uPhysical ubar hh ht hu0Physical S D hS hD
  obtain ⟨ubar0, hh0, hu0bar0, hnorm⟩ :=
    exists_recenteredFlatComparator (originCube d ((n : ℤ) - 2)) c
      u0 uPhysical ubar hh ht hu0Physical
  rw [hnorm]
  exact hloop M s hs L n hnL omega c z hcontain hgood g hg u0 v0 ubar0
    hu0 hv0 huv0 hh0 hu0bar0 S D hS hD

/-- Named scalar readout of the two flat-comparator error terms. -/
noncomputable def flatComparatorGoodEventLoopBound
    (C : ℝ≥0∞) (d : ℕ) [NeZero d] (n : ℕ) (sigma : ℝ)
    (smid s1 s2 : FractionalOrder) (E S D : ℝ)
    (Q : TriadicCube d) (g : Vec d → Vec d) : ℝ :=
  (Section6Dirichlet.dirichletSpectralReadoutConstant smid d *
      ENNReal.ofReal (centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ *
        (flatComparatorLocalCoarseBound C sigma smid s1 s2 E E S D
          ((n : ℤ) - 3)).toReal)).toReal +
    unitDirichletPoincareConst d * (3 : ℝ) ^ ((n : ℤ) - 2) *
      (d : ℝ) * sigma⁻¹ *
        (Real.sqrt (Fintype.card (Fin d) : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q smid.1 g)

/-- The same residue estimate on the literal well-placed comparator domain
returned by `BoundaryComparatorParentPrice`. -/
theorem exists_normalizedL2On_sub_wellPlacedFlatComparator_le_goodEventLoop
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
      ∀ u0 v0 : H1Function (openCubeSet Q),
        IsForcedEquation Q (A.coeffOn Q) u0 g →
        IsScalarForcedEquation Q sigma v0 g →
        HasH10Difference Q u0 v0 →
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
          flatComparatorGoodEventLoopBound C d n sigma smid s1 s2 E S D Q g := by
  obtain ⟨C, hCtop, hloop⟩ :=
    exists_cubeLpNorm_sub_unitHarmonic_le_flatComparatorGoodEvent d hd
  refine ⟨C, hCtop, ?_⟩
  intro M s hs L m n hnL omega q z hcontain hgood
  dsimp only
  intro hkm g hg u0 v0 hu0 hv0 huv0 uPhysical ubar hh ht hu0Physical S D hS hD
  obtain ⟨ubar0, hh0, hu0bar0, hnorm⟩ :=
    exists_recenteredFlatComparator_wellPlaced hkm q u0 uPhysical ubar
      hh ht hu0Physical
  rw [hnorm]
  have hout := hloop M s hs L n hnL omega
    (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) ((n : ℤ) - 2)) z
    hcontain hgood g hg u0 v0 ubar0 hu0 hv0 huv0 hh0 hu0bar0 S D hS hD
  simpa only [flatComparatorGoodEventLoopBound] using hout

/-- Source-replacement specialization of the well-placed loop.  The scalar
comparison solution is constructed internally from the physical local
solution, leaving only the heterogeneous equation in the interface. -/
theorem exists_normalizedL2On_sub_wellPlacedFlatComparator_le_goodEventLoop_of_forced
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
          flatComparatorGoodEventLoopBound C d n sigma smid s1 s2 E S D Q g := by
  obtain ⟨C, hCtop, hloop⟩ :=
    exists_normalizedL2On_sub_wellPlacedFlatComparator_le_goodEventLoop d hd
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
  exact hloop M s hs L m n hnL omega q z hcontain hgood hkm g hg
    u0 v0 hu0 hv0 huv0 uPhysical ubar hh ht hu0Physical S D hS hD

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
