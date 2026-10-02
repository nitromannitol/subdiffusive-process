import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.LocalComparisonDatum
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorTransport




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The frozen pointwise boundary relation gives the physical `H¹₀` carrier
required by the translated flat-comparator theorem. -/
theorem memH10_sub_physical_of_hasZeroTraceDifferenceOn
    {W : Set (Vec d)} {v uD : H1Function W} {u : Vec d → ℝ}
    (htrace : HasZeroTraceDifferenceOn W v uD)
    (huD : ∀ x, uD.toFun x = u x) :
    MemH10 W (fun x ↦ v.toFun x - u x) := by
  obtain ⟨w, hw, _⟩ := htrace
  refine ⟨w, funext fun x ↦ ?_⟩
  rw [hw x, huD x]
  ring

omit [NeZero d] in
/-- Restrict a harmonic-comparison norm from its translated parent to the
frozen inner window.  The integrability premise is discharged from the two
`H1Function` carriers, while the physical representative is retained
pointwise. -/
theorem normalizedL2On_sub_physical_le_of_subset
    {W V : Set (Vec d)} {uD v : H1Function W} {u : Vec d → ℝ}
    (huD : ∀ x, uD.toFun x = u x) (hVW : V ⊆ W)
    (hWpos : 0 < (volume W).toReal) (hVpos : 0 < (volume V).toReal) :
    normalizedL2On V (fun x ↦ u x - v.toFun x) ≤
      Real.sqrt ((volume W).toReal / (volume V).toReal) *
        normalizedL2On W (fun x ↦ u x - v.toFun x) := by
  have hmem : MemLp (fun x ↦ u x - v.toFun x) 2 (volume.restrict W) := by
    have hrewrite : (fun x ↦ u x - v.toFun x) =
        fun x ↦ uD.toFun x - v.toFun x := by
      funext x
      rw [huD x]
    rw [hrewrite]
    exact uD.memL2.sub v.memL2
  exact Section6Iteration.normalizedL2On_le_of_subset
    hVW hWpos hVpos hmem.integrable_sq

/-- Restore the frozen good-event indicator after proving the comparison on
the good event.  This keeps the event split outside the analytic comparison
lemma. -/
theorem indicatorValue_le_of_mem_imp
    {Omega : Type*} (E : Set Omega) (X : Omega → ℝ) (omega : Omega)
    {B : ℝ} (hB : 0 ≤ B) (hmem : omega ∈ E → X omega ≤ B) :
    indicatorValue E X omega ≤ B := by
  by_cases h : omega ∈ E
  · rw [Section6ExcessDecay.indicatorValue_of_mem h]
    exact hmem h
  · rw [Section6ExcessDecay.indicatorValue_of_notMem h]
    exact hB

/-- Local source-comparison datum with the physical value, gradient, and force
translation identities retained for the final comparison readout. -/
theorem exists_localSourceComparisonDatum_of_dirichlet_retained
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (m : ℕ) (k : ℤ) (y : Vec d) (s : FractionalOrder)
    (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
    (g : Vec d → Vec d)
    (hdir : IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
      (originCube d (m : ℤ)) u h g)
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
  have huDt : IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
      (translateSet y (openCubeSet (originCube d k))) uDt g :=
    isDivFormWeakSolutionOn_restrict
      (isOpenBoundedConvexDomain_openCubeSet (originCube d (m : ℤ))).isOpen
      hDopen hsubt hdir.2
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

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
