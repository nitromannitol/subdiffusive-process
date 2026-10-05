module

public import SubdiffusiveProcess.Analysis.SmoothDualComparison
public import SubdiffusiveProcess.Analysis.SmoothDualCutoffEntry
public import SubdiffusiveProcess.Analysis.InteriorComparisonErrorTransport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorForcing
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorTransport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior.RetainedDatum

@[expose] public section

/-!
# The deterministic interior comparison loop

Deterministic (arbitrary scalar coefficient) twin of the GMC good-event
smooth-dual loop
`SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.SmoothDualComparison.
exists_normalizedL2On_sub_flatComparator_le_cutoffGoodEventLoop_of_forced_smoothDual_neZero`
(`SubdiffusiveProcess/Analysis/SmoothDualCutoffEntry.lean`).  It compares the
`dataY`-forced solution `u0` against the unit-harmonic replacement through the
`a0`-forced scalar replacement `v0`:

`u0` (forced, coefficient `dataY`) → `v0` (forced, scalar `a0`, same trace) →
`ubar0` (unit harmonic, same trace as `v0`).

The first leg is `SmoothDualComparison`
(`exists_cubeLpNorm_sub_le_flatComparatorSmoothManuscriptBound`, deterministic,
arbitrary `TriadicCoeffFamily`).  The second leg is `FlatComparatorForcing`'s
`cubeLpNorm_scalarForced_sub_unitHarmonic_le_positiveBesov` (also
deterministic).

 `aux_icc_localSourceComparisonDatum` is the deterministic twin of
`SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior.
exists_localSourceComparisonDatum_weak_retained` (`RetainedDatum.lean`) with
`aCutoff` replaced by an arbitrary `ScalarTriadicCoeffData`; `aux_icc_loop`
is the twin of the loop theorem cited above with the good-event error
replaced by a Chapter 2 error hypothesis.
-/

namespace SubdiffusiveProcess.InteriorComparisonEngine

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube Mat
open Homogenization.Book
open Homogenization.Book.Ch03 Homogenization.Book.Ch03.ABK26 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open _root_.SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.SmoothDualComparison
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

variable {d : ℕ} [NeZero d]

/-- **Local source-comparison datum for an arbitrary scalar coefficient.**
Restrict the weak solution to the translated cube `y + 𝔠_k`, untranslate it,
and replace the coefficient by the constant `sigma`, retaining the pointwise
value and gradient identities. -/
theorem aux_icc_localSourceComparisonDatum
    {a : Vec d → ℝ} (m : ℕ) (k : ℤ) (y : Vec d) (s : FractionalOrder)
    (dataY : ScalarTriadicCoeffData (fun q => a (q + y)))
    (u : H1Function (openCubeSet (originCube d (m : ℤ))))
    (g : Vec d → Vec d)
    (hu : IsDivFormWeakSolutionOn a (cube d (m : ℤ)) u g)
    (hg : Ch03.ABK26.MemCubeEuclideanFullWsp
      (originCube d (m : ℤ)) s FiniteLpExponent.two g)
    (hsub : translatedCube d k y ⊆ openCubeSet (originCube d (m : ℤ)))
    (sigma : ℝ) (hsigma : 0 < sigma) :
    ∃ g0 : Vec d → Vec d,
      Ch03.ABK26.MemCubeEuclideanFullWsp
          (originCube d k) s FiniteLpExponent.two g0 ∧
      (∀ x, g0 x = g (x + y)) ∧
      ∃ u0 v0 : H1Function (openCubeSet (originCube d k)),
        Ch03.ABK26.IsForcedEquation (originCube d k)
            (dataY.toTriadicCoeffFamily.coeffOn (originCube d k)) u0 g0 ∧
        Ch03.ABK26.IsScalarForcedEquation (originCube d k) sigma v0 g0 ∧
        Ch03.ABK26.HasH10Difference (originCube d k) u0 v0 ∧
        (∀ x, u0.toFun x = u.toFun (x + y)) ∧
        (∀ x, u0.grad x = u.grad (x + y)) := by
  have hD : translatedCube d k y =
      translateSet y (openCubeSet (originCube d k)) := by
    rw [translatedCube, cube,
      SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.image_add_eq_translateSet]
  have hDopen : IsOpen (translateSet y (openCubeSet (originCube d k))) :=
    (isOpenBoundedConvexDomain_openCubeSet (originCube d k)).translateSet y |>.isOpen
  have hsubt : translateSet y (openCubeSet (originCube d k)) ⊆
      openCubeSet (originCube d (m : ℤ)) := by
    rw [← hD]
    exact hsub
  let uDt : H1Function (translateSet y (openCubeSet (originCube d k))) :=
    u.restrict hDopen hsubt
  have huDt : IsDivFormWeakSolutionOn a
      (translateSet y (openCubeSet (originCube d k))) uDt g :=
    isDivFormWeakSolutionOn_restrict
      (isOpenBoundedConvexDomain_openCubeSet (originCube d (m : ℤ))).isOpen
      hDopen hsubt hu
  let g0 : Vec d → Vec d := fun x ↦ g (x + y)
  have hg0 : Ch03.ABK26.MemCubeEuclideanFullWsp
      (originCube d k) s FiniteLpExponent.two g0 :=
    memCubeEuclideanFullWsp_translate_of_subset
      (originCube d k) (originCube d (m : ℤ)) y s
      FiniteLpExponent.two g hsubt hg
  have hg0Two : MemLp g0 2 (normalizedCubeMeasure (originCube d k)) :=
    Ch03.ABK26.MemCubeEuclideanFullWsp.memLpTwo (by norm_num) hg0
  have hg0Open : MemVectorL2 (openCubeSet (originCube d k)) g0 := by
    have hg0Cube : MemVectorL2 (cubeSet (originCube d k)) g0 :=
      memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure (originCube d k) hg0Two
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using! hg0Cube
  let u0 : H1Function (openCubeSet (originCube d k)) := H1Function.untranslate y uDt
  let v0 : H1Function (openCubeSet (originCube d k)) :=
    sourceForcedReplacement (scalarConstantCoeffMatrix (d := d) hsigma) u0 hg0Open
  have hu0 : Ch03.ABK26.IsForcedEquation (originCube d k)
      (dataY.toTriadicCoeffFamily.coeffOn (originCube d k)) u0 g0 :=
    aux_icc_isForcedEquation_scalarData_untranslate (originCube d k) y dataY huDt
  have hv0 : Ch03.ABK26.IsScalarForcedEquation (originCube d k) sigma v0 g0 :=
    isScalarForcedEquation_sourceForcedReplacement hsigma u0 hg0Open
  have huv : Ch03.ABK26.HasH10Difference (originCube d k) u0 v0 :=
    hasH10Difference_sourceForcedReplacement
      (scalarConstantCoeffMatrix (d := d) hsigma) u0 hg0Open
  refine ⟨g0, hg0, fun _ ↦ rfl, u0, v0, hu0, hv0, huv, ?_, ?_⟩
  · intro x
    rfl
  · intro x
    rfl

/-- **The deterministic smooth-dual loop.**  For a `dataY`-forced `u0` on
`𝔠_{n-2}` whose translate is compared with a unit harmonic `ubar` on the
translated cube `y + 𝔠_{n-2}`, with the anchored error `E` of `dataY` against
the constant `a0`, the normalized `L²` distance is bounded by the smooth-dual
loop carrier.  The constant `C` is chosen before all data. -/
theorem aux_icc_loop (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (s : ℝ) (hs0 : 0 < s) (hs4 : s ≤ 1 / 4) (n : ℕ) (y : Vec d)
        (a : Vec d → ℝ) (dataY : ScalarTriadicCoeffData (fun q => a (q + y)))
        (a0 : ℝ), 0 < a0 →
      let Q := originCube d ((n : ℤ) - 2)
      let s1 : FractionalOrder := ⟨s / 3, by positivity, by linarith⟩
      let smid : FractionalOrder := ⟨s / 2, by positivity, by linarith⟩
      let s2 : FractionalOrder := ⟨s, hs0, by linarith⟩
      ∀ (g : Vec d → Vec d), MemCubeEuclideanFullWsp Q s2 FiniteLpExponent.two g →
      ∀ u0 : H1Function (openCubeSet Q),
        IsForcedEquation Q (dataY.toTriadicCoeffFamily.coeffOn Q) u0 g →
      ∀ (uPhysical : Vec d → ℝ)
        (ubar : H1Function (translateSet y (openCubeSet Q))),
        IsUnitWeaklyHarmonicOn (translateSet y (openCubeSet Q)) ubar →
        MemH10 (translateSet y (openCubeSet Q))
          (fun p ↦ ubar.toFun p - uPhysical p) →
        (∀ p, u0.toFun p = uPhysical (p + y)) →
      ∀ E S D : ℝ,
        Ch02.HomogenizationErrorOnCube Q (s / 6) Ch02.MultiscaleExponent.infinity
          (Ch02.MultiscaleExponent.finite 2) dataY.toTriadicCoeffFamily
          (scalarMatrix (d := d) a0) ≤ E →
        weightedLocalSymmetricEnergyLp Q (Q.scale - 1) (by omega)
          (dataY.toTriadicCoeffFamily.coeffOn Q) u0 s1 smid FiniteLpExponent.two ≤
            ENNReal.ofReal S →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm Q s2
          FiniteLpExponent.two g ≤ ENNReal.ofReal D →
        normalizedL2On (translateSet y (openCubeSet Q))
            (fun p ↦ uPhysical p - ubar.toFun p) ≤
          flatComparatorSmoothGoodEventLoopBound C d n a0 smid s1 s2 E S D Q g := by
  obtain ⟨C, hCtop, hleg1⟩ :=
    SmoothDualComparison.exists_cubeLpNorm_sub_le_flatComparatorSmoothManuscriptBound d hd
  refine ⟨C, hCtop, ?_⟩
  intro s hs0 hs4 n y a dataY a0 ha0
  dsimp only
  intro g hg u0 hu0 uPhysical ubar hh ht hu0Physical E S D hE hS hD
  have hgTwo : MemLp g 2 (normalizedCubeMeasure (originCube d ((n : ℤ) - 2))) :=
    MemCubeEuclideanFullWsp.memLpTwo (by norm_num) hg
  have hgCube : MemVectorL2 (cubeSet (originCube d ((n : ℤ) - 2))) g :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure
      (originCube d ((n : ℤ) - 2)) hgTwo
  have hgOpen : MemVectorL2 (openCubeSet (originCube d ((n : ℤ) - 2))) g := by
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using! hgCube
  let v0 := sourceForcedReplacement
    (scalarConstantCoeffMatrix (d := d) ha0) u0 hgOpen
  have hv0 : IsScalarForcedEquation (originCube d ((n : ℤ) - 2)) a0 v0 g :=
    isScalarForcedEquation_sourceForcedReplacement ha0 u0 hgOpen
  have huv0 : HasH10Difference (originCube d ((n : ℤ) - 2)) u0 v0 :=
    hasH10Difference_sourceForcedReplacement
      (scalarConstantCoeffMatrix (d := d) ha0) u0 hgOpen
  obtain ⟨ubar0, hh0, hu0bar0, hnorm⟩ :=
    exists_recenteredFlatComparator (originCube d ((n : ℤ) - 2)) y
      u0 uPhysical ubar hh ht hu0Physical
  rw [hnorm]
  have h1 := hleg1 ((n : ℤ) - 2) s hs0 (by linarith) hs4
    dataY.toTriadicCoeffFamily a0 ha0 g hg u0 v0 hu0 hv0 huv0 E S D hE
    (by simpa [originCube] using! hS) hD
  have hthree : ((n : ℤ) - 2 - 1) = (n : ℤ) - 3 := by ring
  rw [hthree] at h1
  have hreg : ForceBesovRegularity (originCube d ((n : ℤ) - 2)) (s / 2) g :=
    forceBesovRegularity_of_memCubeEuclideanFullWsp_lt
      (t := (⟨s / 2, by positivity, by linarith⟩ : FractionalOrder)) hg
      (by show s / 2 < s; linarith)
  have hvh : HasH10Difference (originCube d ((n : ℤ) - 2)) v0 ubar0 :=
    hasH10Difference_trans (hasH10Difference_symm huv0) hu0bar0
  have h2 := cubeLpNorm_scalarForced_sub_unitHarmonic_le_positiveBesov
    ((n : ℤ) - 2) ha0 hreg hv0 hh0 hvh
  have hsum := cubeLpNorm_sub_unitHarmonic_le_add
    (originCube d ((n : ℤ) - 2)) u0 v0 ubar0 h1 h2
  simpa only [flatComparatorSmoothGoodEventLoopBound] using! hsum

end

end SubdiffusiveProcess.InteriorComparisonEngine
