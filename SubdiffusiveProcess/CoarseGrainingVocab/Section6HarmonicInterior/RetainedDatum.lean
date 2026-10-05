module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.LocalComparisonDatum

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior

open Homogenization Homogenization.Book MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **Retained local comparison datum, datum-free.**  Value-, gradient- and
force-retaining companion of
`Section6HarmonicApproximation.exists_localSourceComparisonDatum`, consuming only
the weak equation and the force regularity. -/
theorem exists_localSourceComparisonDatum_weak_retained
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (m : ℕ) (k : ℤ) (y : Vec d) (s : FractionalOrder)
    (u : H1Function (openCubeSet (originCube d (m : ℤ))))
    (g : Vec d → Vec d)
    (hu : IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
      (cube d (m : ℤ)) u g)
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
            ((aCutoffFamily M L (translatePotentialSample y omega)).coeffOn
              (originCube d k)) u0 g0 ∧
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
  have huDt : IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
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
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using hg0Cube
  let u0 : H1Function (openCubeSet (originCube d k)) := H1Function.untranslate y uDt
  let v0 : H1Function (openCubeSet (originCube d k)) :=
    sourceForcedReplacement (scalarConstantCoeffMatrix (d := d) hsigma) u0 hg0Open
  have hu0 : Ch03.ABK26.IsForcedEquation (originCube d k)
      ((aCutoffFamily M L (translatePotentialSample y omega)).coeffOn
        (originCube d k)) u0 g0 :=
    isForcedEquation_aCutoff_untranslate M L omega (originCube d k) y huDt
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

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior
