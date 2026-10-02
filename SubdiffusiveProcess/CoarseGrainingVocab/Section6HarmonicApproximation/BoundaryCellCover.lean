import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEnergyReadout
import Homogenization.Besov.Localization
import Homogenization.Book.Ch01.Theorems.NormScaling

/-!
# The fixed `9^d` descendant cover

The scale-`k` translated cube is partitioned, up to its null boundaries, by
the depth-two descendants of the origin cube.  The normalized integral is
therefore their exact finite average.

PROVENANCE: this is the descendant-partition form of the fixed cover used in
`Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryAssemblyEnergy.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03
open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Open- and closed-cube normalized averages agree. -/
theorem volumeAverage_openCubeSet_eq_cubeAverage
    (Q : TriadicCube d) (f : Vec d → ℝ) :
    volumeAverage (openCubeSet Q) f = cubeAverage Q f := by
  unfold volumeAverage cubeAverage
  rw [volume_openCubeSet_toReal]
  congr 1
  exact (setIntegral_cubeSet_eq_setIntegral_openCubeSet (Q := Q) (f := f)).symm

/-- A cube average after shifting the integrand is the physical average on
the translated open cube. -/
theorem cubeAverage_comp_addRight_eq_volumeAverage_translateSet
    (Q : TriadicCube d) (y : Vec d) (f : Vec d → ℝ) :
    cubeAverage Q (fun x => f (x + y)) =
      volumeAverage (translateSet y (openCubeSet Q)) f := by
  rw [← volumeAverage_openCubeSet_eq_cubeAverage,
    Ch01.volumeAverage_translateSet_eq_comp_addRight]

/-- Exact finite-average decomposition over the depth-two descendants.  Its
cardinality is `(3^d)^2 = 9^d`. -/
theorem volumeAverage_translatedCube_eq_depthTwoDescendantsAverage
    (k : ℤ) (y : Vec d) (f : Vec d → ℝ)
    (hf : IntegrableOn (fun x => f (x + y))
      (cubeSet (originCube d k)) volume) :
    volumeAverage (translatedCube d k y) f =
      descendantsAverage (originCube d k) 2 (fun R =>
        volumeAverage (translateSet y (openCubeSet R)) f) := by
  rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet,
    Ch01.volumeAverage_translateSet_eq_comp_addRight,
    volumeAverage_openCubeSet_eq_cubeAverage]
  rw [cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
    (originCube d k) 2 (fun x => f (x + y)) hf]
  apply congrArg (descendantsAverage (originCube d k) 2)
  funext R
  exact cubeAverage_comp_addRight_eq_volumeAverage_translateSet R y f

/-- The depth-two descendant count is the manuscript's literal `9^d`. -/
theorem depthTwoDescendants_card_eq_nine_pow (Q : TriadicCube d) :
    (descendantsAtDepth Q 2).card = 9 ^ d := by
  rw [descendantsAtDepth_card]
  calc
    (3 ^ d) ^ 2 = 3 ^ d * 3 ^ d := by rw [pow_two]
    _ = (3 * 3) ^ d := by rw [mul_pow]
    _ = 9 ^ d := by norm_num

/-- The physical centre of a descendant belongs to its translated open cube. -/
theorem translated_descendantCentre_mem
    (y : Vec d) (R : TriadicCube d) :
    y + triadicCubeShift R ∈ translateSet y (openCubeSet R) := by
  rw [openCubeSet_eq_translateSet_originCube_of_triadicCube,
    translateSet_translateSet]
  have hzero : (0 : Vec d) ∈ openCubeSet (originCube d R.scale) := by
    simpa [cube] using Section6ExcessDecay.zero_mem_cube d R.scale
  refine ⟨0, hzero, ?_⟩
  simp [add_comm]

/-- A physical translated descendant is contained in the translated parent. -/
theorem translate_descendant_openCubeSet_subset_parent
    {Q R : TriadicCube d} {j : ℕ} (y : Vec d)
    (hR : R ∈ descendantsAtDepth Q j) :
    translateSet y (openCubeSet R) ⊆ translateSet y (openCubeSet Q) := by
  intro x hx
  rw [mem_translateSet_iff_sub_mem] at hx ⊢
  exact openCubeSet_subset_of_mem_descendantsAtDepth hR hx

/-- A depth-two descendant of the scale-`k` origin cube has scale `k-2`. -/
theorem scale_eq_sub_two_of_mem_depthTwo
    {k : ℤ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d k) 2) :
    R.scale = k - 2 := by
  simpa using scale_eq_sub_of_mem_descendantsAtDepth hR

/-- The physical open descendant is exactly the translated scale-`k-2` cube
centred at `y + triadicCubeShift R`. -/
theorem translate_descendant_openCubeSet_eq_translatedCube
    {k : ℤ} (y : Vec d) {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d k) 2) :
    translateSet y (openCubeSet R) =
      translatedCube d (k - 2) (y + triadicCubeShift R) := by
  rw [openCubeSet_eq_translateSet_originCube_of_triadicCube,
    translateSet_translateSet, translatedCube, cube,
    Section6SchauderDatum.image_add_eq_translateSet,
    scale_eq_sub_two_of_mem_depthTwo hR]
  congr 1
  abel

/-- If the translated parent is contained in the ambient domain, a physical
depth-two descendant is exactly the corresponding truncated cell. -/
theorem translate_descendant_openCubeSet_eq_truncatedCube
    {m k : ℤ} {y : Vec d} {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d k) 2)
    (hparent : translateSet y (openCubeSet (originCube d k)) ⊆ cube d m) :
    translateSet y (openCubeSet R) =
      truncatedCube d m (k - 2) (y + triadicCubeShift R) := by
  have hcell : translateSet y (openCubeSet R) ⊆ cube d m :=
    (translate_descendant_openCubeSet_subset_parent y hR).trans hparent
  have htranslated : translatedCube d (k - 2) (y + triadicCubeShift R) ⊆ cube d m := by
    simpa [translate_descendant_openCubeSet_eq_translatedCube y hR] using hcell
  rw [Section6ExcessDecay.truncatedCube_eq, Set.inter_eq_left.mpr htranslated]
  exact translate_descendant_openCubeSet_eq_translatedCube y hR

/-- The physical centre of a depth-two descendant lies in every set which
contains the translated parent. -/
theorem translated_descendantCentre_mem_of_parent_subset
    {k : ℤ} {y : Vec d} {R : TriadicCube d} {U : Set (Vec d)}
    (hR : R ∈ descendantsAtDepth (originCube d k) 2)
    (hparent : translateSet y (openCubeSet (originCube d k)) ⊆ U) :
    y + triadicCubeShift R ∈ U :=
  hparent (translate_descendant_openCubeSet_subset_parent y hR
    (translated_descendantCentre_mem y R))

/-- The projected scale-`n-2` cube attached to a depth-two child of the
scale-`n-2` comparison cube stays inside the next truncated window. -/
theorem projectedCube_of_depthTwo_subset_nextWindow
    {m n : ℤ} {x y : Vec d} {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d (n - 2)) 2)
    (hparent : translateSet y (openCubeSet (originCube d (n - 2))) ⊆
      truncatedCube d m (n - 1) x)
    (hnm : n - 2 ≤ m) :
    translatedCube d (n - 2)
        (Section6ExcessDecay.wellPlacedCentre
          (y + triadicCubeShift R) m (n - 2)) ⊆
      truncatedCube d m n x := by
  apply translatedCube_wellPlacedCentre_subset_nextWindow_of_mem
  · exact translated_descendantCentre_mem_of_parent_subset hR hparent
  · exact hnm

/-- The physical cutoff energy on a translated comparison cube is the exact
finite average of its depth-two descendant-cell energies. -/
theorem cutoffEnergy_translatedCube_eq_depthTwoDescendantsAverage
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {m k : ℤ} {y : Vec d}
    (u : H1Function (openCubeSet (originCube d m)))
    (hparent : translatedCube d k y ⊆ openCubeSet (originCube d m)) :
    normalizedSetAverage (translatedCube d k y) (fun x =>
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) =
      descendantsAverage (originCube d k) 2 (fun R =>
        normalizedSetAverage (translateSet y (openCubeSet R)) (fun x =>
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x))) := by
  let f : Vec d → ℝ := fun x =>
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)
  have hDmeas : MeasurableSet (translatedCube d k y) :=
    (Section6ExcessDecay.isOpenBoundedConvexDomain_translatedCube d k y).isOpen.measurableSet
  have hint : IntegrableOn f (translatedCube d k y) :=
    integrableOn_cutoffEnergy_of_subset_originCube M L omega m
      (translatedCube d k y) u hDmeas hparent
  have hiff := (measurePreserving_add_right (volume : Measure (Vec d)) y).integrableOn_image
    (Homeomorph.addRight y).measurableEmbedding (f := f)
      (s := openCubeSet (originCube d k))
  rw [image_addRight_eq_translateSet] at hiff
  have htranslated : translateSet y (openCubeSet (originCube d k)) =
      translatedCube d k y := by
    rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet]
  rw [htranslated] at hiff
  have hopen : IntegrableOn (fun x => f (x + y))
      (openCubeSet (originCube d k)) := by
    simpa only [Function.comp_apply] using hiff.mp hint
  have hcube : IntegrableOn (fun x => f (x + y))
      (cubeSet (originCube d k)) :=
    integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr hopen
  simpa only [f] using
    volumeAverage_translatedCube_eq_depthTwoDescendantsAverage k y f hcube

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
