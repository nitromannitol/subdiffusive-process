import SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily.TranslationIsometry
import SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily.NestedWeightBridge




open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily

open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-- The concentric parent carrier, in axis-cube form. -/
def nfAxisParent (d : ℕ) (z : Vec d) (m : ℤ) : Set (Vec d) :=
  axisCube (oneStepCenteredAxisCorner z m) (cubeScaleFactor (originCube d m))

theorem nfAxisParent_eq_translateSet (d : ℕ) (z : Vec d) (m : ℤ) :
    nfAxisParent d z m = translateSet z (openCubeSet (originCube d m)) :=
  (translateSet_openCubeSet_originCube_eq_axisCube z m).symm

theorem nfAxisParent_side_pos (d : ℕ) (m : ℤ) :
    0 < cubeScaleFactor (originCube d m) := by
  simpa [cubeScaleFactor] using
    (zpow_pos (show (0 : ℝ) < 3 by norm_num) m)

/-! ## The gradient telescope on a concentric parent -/

/-- The local Neumann--Dirichlet axis remainder is, gradientwise, the
difference of the two stationary local solutions. -/
theorem nfAxisNeumannDirichletRemainder_grad_eq_sub [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (omega : NFSample d) (p z : Vec d) (m : ℤ) (hh : 0 < h) :
    (oneStepNeumannDirichletAxisRemainder M n h omega p z m hh).grad =
      fun x => (oneStepNeumannAxisLocalSolution M n h omega p z m hh).grad x -
        (oneStepDirichletAxisLocalSolution M n h omega p z m hh).grad x := by
  have hcast := nfCastH1Domain_grad
    (translateSet_openCubeSet_originCube_eq_axisCube z m)
    (((oneStepOriginNeumannSolution M n h p m
        (translatePotentialSequence z omega) hh).toH1Function -
      (oneStepOriginDirichletSolution M n h p m
        (translatePotentialSequence z omega) hh).toH1Function).translate z)
  refine hcast.trans ?_
  funext x
  rw [oneStepNeumannAxisLocalSolution_grad,
    oneStepDirichletAxisLocalSolution_grad]
  simp only [oneStepTranslatedNeumannSolution,
    oneStepTranslatedDirichletSolution,
    H1MeanZeroFunction.translate_toH1Function,
    H10Function.translate_toH1Function,
    H1Function.translate_grad, H1Function.sub_grad]

/-- The three-piece gradient telescope on a concentric parent. -/
theorem nfAxis_grad_split [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (omega : NFSample d) (p z : Vec d) (K m : ℤ)
    (hsub : translateSet z (openCubeSet (originCube d m)) ⊆
      openCubeSet (originCube d K)) (hh : 0 < h) :
    (oneStepNeumannAxisLargeRestriction M n h omega p z K m hsub hh).grad =
      fun x =>
        (oneStepDirichletAxisLocalSolution M n h omega p z m hh).grad x +
          ((oneStepNeumannDirichletAxisRemainder M n h omega p z m hh).grad x +
            (oneStepNeumannAxisRemainder M n h omega p z K m hsub hh).grad x) := by
  funext x
  funext i
  rw [nfAxisNeumannDirichletRemainder_grad_eq_sub M n h omega p z m hh]
  simp only [oneStepNeumannAxisRemainder, H1Function.sub_grad,
    Pi.sub_apply, Pi.add_apply]
  ring

/-! ## The persistent Dirichlet Hessian on a concentric parent -/

theorem nfAxisDirichletLocal_grad_translate [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (omega : NFSample d) (p z : Vec d) (m : ℤ) (hh : 0 < h) :
    (oneStepDirichletAxisLocalSolution M n h omega p z m hh).grad =
      ((oneStepOriginDirichletSolution M n h p m
        (translatePotentialSequence z omega) hh).toH1Function.translate z
          ).grad := by
  rw [oneStepDirichletAxisLocalSolution_grad]
  unfold oneStepTranslatedDirichletSolution
  rw [H10Function.translate_toH1Function]

/-- Samplewise weak Hessian for the persistent Dirichlet member on a
concentric parent. -/
theorem nonempty_nfAxisDirichletLocal_parentHessian
    (d : ℕ) [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p z : Vec d) (m : ℤ)
    (hh : 0 < h) :
    Nonempty (∀ omega : NFSample d,
      HasWeakHessianOn (nfAxisParent d z m)
        (oneStepDirichletAxisLocalSolution M n h omega p z m hh)) := by
  obtain ⟨_C, _hCtop, hpack⟩ :=
    exists_measurable_oneStepCanonicalDirichlet_cellB d
  obtain ⟨V, hV, _hmeas, _hbound⟩ := hpack M n h p m hh
  refine ⟨fun omega => ?_⟩
  let HO : HasWeakHessianOn (openCubeSet (originCube d m))
      (oneStepOriginDirichletSolution M n h p m
        (translatePotentialSequence z omega) hh).toH1Function :=
    weakHessianOfCubeVectorW1pFour
      (V (translatePotentialSequence z omega))
      (hV (translatePotentialSequence z omega))
  refine nfWeakHessianOfGradEq ?_
    (nfCastWeakHessian (translateSet_openCubeSet_originCube_eq_axisCube z m)
      (HO.translate z))
  rw [nfCastH1Domain_grad]
  exact nfAxisDirichletLocal_grad_translate M n h omega p z m hh

/-! ## Measurability on a concentric parent -/

theorem measurable_nfAxisLocalNeumann_grad [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p z : Vec d) (m : ℤ)
    (hh : 0 < h) :
    Measurable fun omega : NFSample d =>
      (oneStepNeumannAxisLocalSolution M n h omega p z m hh
        ).gradToHilbertVectorL2 :=
  measurable_gradToHilbertVectorL2_of_grad_eq_restrict
    (translateSet_openCubeSet_originCube_eq_axisCube z m).ge
    (fun omega =>
      (oneStepTranslatedNeumannSolution M n h p z m omega hh).toH1Function)
    (fun omega => oneStepNeumannAxisLocalSolution M n h omega p z m hh)
    (measurable_oneStepTranslatedNeumannGradL2 M n h p z m hh)
    (fun omega => oneStepNeumannAxisLocalSolution_grad M n h omega p z m hh)

theorem measurable_nfAxisLocalDirichlet_grad [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p z : Vec d) (m : ℤ)
    (hh : 0 < h) :
    Measurable fun omega : NFSample d =>
      (oneStepDirichletAxisLocalSolution M n h omega p z m hh
        ).gradToHilbertVectorL2 :=
  measurable_gradToHilbertVectorL2_of_grad_eq_restrict
    (translateSet_openCubeSet_originCube_eq_axisCube z m).ge
    (fun omega =>
      (oneStepTranslatedDirichletSolution M n h p z m omega hh).toH1Function)
    (fun omega => oneStepDirichletAxisLocalSolution M n h omega p z m hh)
    (measurable_oneStepTranslatedDirichletGradL2 M n h p z m hh)
    (fun omega => oneStepDirichletAxisLocalSolution_grad M n h omega p z m hh)

theorem measurable_nfAxisLargeRestriction_grad [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p z : Vec d)
    (K m : ℤ)
    (hsub : translateSet z (openCubeSet (originCube d m)) ⊆
      openCubeSet (originCube d K)) (hh : 0 < h) :
    Measurable fun omega : NFSample d =>
      (oneStepNeumannAxisLargeRestriction M n h omega p z K m hsub hh
        ).gradToHilbertVectorL2 := by
  have hsubAxis : nfAxisParent d z m ⊆ openCubeSet (originCube d K) := by
    rw [nfAxisParent_eq_translateSet]
    exact hsub
  exact measurable_gradToHilbertVectorL2_of_grad_eq_restrict hsubAxis
    (fun omega =>
      (oneStepOriginNeumannSolution M n h p K omega hh).toH1Function)
    (fun omega =>
      oneStepNeumannAxisLargeRestriction M n h omega p z K m hsub hh)
    (measurable_twoRadiusLarge_bigGrad M n h p K hh)
    (fun omega =>
      oneStepNeumannAxisLargeRestriction_grad M n h omega p z K m hsub hh)

theorem measurable_nfAxisNeumannDirichletRemainder_grad [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p z : Vec d) (m : ℤ)
    (hh : 0 < h) :
    Measurable fun omega : NFSample d =>
      (oneStepNeumannDirichletAxisRemainder M n h omega p z m hh
        ).gradToHilbertVectorL2 := by
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have hdiff : Measurable fun omega : NFSample d =>
      H1Function.gradToHilbertVectorL2
        (oneStepNeumannAxisLocalSolution M n h omega p z m hh -
          oneStepDirichletAxisLocalSolution M n h omega p z m hh) := by
    have heq : (fun omega : NFSample d =>
        H1Function.gradToHilbertVectorL2
          (oneStepNeumannAxisLocalSolution M n h omega p z m hh -
            oneStepDirichletAxisLocalSolution M n h omega p z m hh)) =
        fun omega =>
          (oneStepNeumannAxisLocalSolution M n h omega p z m hh
            ).gradToHilbertVectorL2 -
          (oneStepDirichletAxisLocalSolution M n h omega p z m hh
            ).gradToHilbertVectorL2 := by
      funext omega
      exact nfGradToHilbertVectorL2_sub _ _
    rw [heq]
    exact (measurable_nfAxisLocalNeumann_grad M n h p z m hh).sub
      (measurable_nfAxisLocalDirichlet_grad M n h p z m hh)
  exact measurable_gradToHilbertVectorL2_of_grad_eq_restrict
    (subset_refl (nfAxisParent d z m))
    (fun omega => oneStepNeumannAxisLocalSolution M n h omega p z m hh -
      oneStepDirichletAxisLocalSolution M n h omega p z m hh)
    (fun omega => oneStepNeumannDirichletAxisRemainder M n h omega p z m hh)
    hdiff
    (fun omega => by
      rw [nfAxisNeumannDirichletRemainder_grad_eq_sub M n h omega p z m hh]
      exact (H1Function.sub_grad _ _).symm)

theorem measurable_nfAxisNeumannRemainder_grad [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p z : Vec d)
    (K m : ℤ)
    (hsub : translateSet z (openCubeSet (originCube d m)) ⊆
      openCubeSet (originCube d K)) (hh : 0 < h) :
    Measurable fun omega : NFSample d =>
      (oneStepNeumannAxisRemainder M n h omega p z K m hsub hh
        ).gradToHilbertVectorL2 := by
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have heq : (fun omega : NFSample d =>
      (oneStepNeumannAxisRemainder M n h omega p z K m hsub hh
        ).gradToHilbertVectorL2) =
      fun omega =>
        (oneStepNeumannAxisLargeRestriction M n h omega p z K m hsub hh
          ).gradToHilbertVectorL2 -
        (oneStepNeumannAxisLocalSolution M n h omega p z m hh
          ).gradToHilbertVectorL2 := by
    funext omega
    exact nfGradToHilbertVectorL2_sub _ _
  rw [heq]
  exact (measurable_nfAxisLargeRestriction_grad M n h p z K m hsub hh).sub
    (measurable_nfAxisLocalNeumann_grad M n h p z m hh)

/-! ## The fixed axis harmonic depth and constant -/

def nfAxisHarmonicDepth (d : ℕ) (hd : 3 ≤ d) : ℕ :=
  (exists_axisCube_harmonic_cellB_bound d hd).choose

def nfAxisHarmonicConst (d : ℕ) (hd : 3 ≤ d) : ℝ :=
  (exists_axisCube_harmonic_cellB_bound d hd).choose_spec.choose

theorem nfAxisHarmonicConst_pos (d : ℕ) (hd : 3 ≤ d) :
    0 < nfAxisHarmonicConst d hd :=
  (exists_axisCube_harmonic_cellB_bound d hd).choose_spec.choose_spec.1

theorem nfAxisHarmonic_cell_hessian (d : ℕ) (hd : 3 ≤ d)
    (z : Vec d) (L : ℝ) (hL : 0 < L) (u : H1Function (axisCube z L))
    (hu : WeakPoissonEquationOn (axisCube z L) u (fun _ ↦ 0))
    (R : TriadicCube d)
    (hRhalf : openCubeSet R ⊆ axisCubeInnerHalf z L)
    (hRinner : openCubeSet R ⊆
      axisCube
        (CubeCalderonZygmund.axisCubeConcentricDepthCorner z L
          (nfAxisHarmonicDepth d hd + 1))
        (CubeCalderonZygmund.axisCubeConcentricDepthSide L
          (nfAxisHarmonicDepth d hd + 1))) :
    ∃ uS : H1Function (axisCubeInnerHalf z L),
      uS.toFun = u.toFun ∧ uS.grad = u.grad ∧
        ∃ H : HasWeakHessianOn (axisCubeInnerHalf z L) uS,
          oneStepCellB R (H.restrict (isOpen_openCubeSet R) hRhalf) ≤
            cubeScaleFactor R * (d : ℝ) ^ 2 *
              ((triadicAxisNormalizedMeasureRatio R
                (CubeCalderonZygmund.axisCubeConcentricDepthSide L
                  (nfAxisHarmonicDepth d hd + 1))) ^
                (1 / (oneStepHarmonicExponent d hd).exponent).toReal).toReal *
              (nfAxisHarmonicConst d hd * L⁻¹ *
                ∑ k : Fin d,
                  (eLpNorm (fun x ↦ u.grad x k) 2
                    (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)
                    ).toReal) :=
  (exists_axisCube_harmonic_cellB_bound d hd).choose_spec.choose_spec.2
    z L hL u hu R hRhalf hRinner

/-- Nested-weight form of the axis harmonic prefactor, with the parent scale
`mm` given directly. -/
theorem nfAxisHarmonic_prefactor_eq_nestedWeight'
    (d : ℕ) (hd : 3 ≤ d) (N : ℕ) (R : TriadicCube d) {mm : ℤ}
    (hmm : R.scale + (N : ℤ) = mm) (S : ℝ) :
    cubeScaleFactor R * (d : ℝ) ^ 2 *
        ((triadicAxisNormalizedMeasureRatio R
          (CubeCalderonZygmund.axisCubeConcentricDepthSide
            (cubeScaleFactor (originCube d mm))
            (nfAxisHarmonicDepth d hd + 1))) ^
          (1 / (oneStepHarmonicExponent d hd).exponent).toReal).toReal *
        (nfAxisHarmonicConst d hd *
          (cubeScaleFactor (originCube d mm))⁻¹ * S) =
      ((d : ℝ) ^ 2 * nfAxisHarmonicConst d hd) *
        oneStepNestedHarmonicWeight d hd (nfAxisHarmonicDepth d hd) N * S := by
  subst hmm
  rw [triadicAxisNormalizedMeasureRatio_nested_eq N
    (nfAxisHarmonicDepth d hd) R rfl]
  rw [oneStepNested_harmonic_prefactor_eq (source := R.scale) N R rfl
    (((ENNReal.ofReal
      (((3 : ℝ) ^ ((N : ℤ) - ((nfAxisHarmonicDepth d hd + 1 : ℕ) : ℤ))) ^ d)) ^
        (1 / (oneStepHarmonicExponent d hd).exponent).toReal).toReal)
    (nfAxisHarmonicConst d hd) S]
  unfold oneStepNestedHarmonicWeight
  ring

/-- The cell of a scale gap `N` sits in the inner half of its concentric
parent. -/
theorem nfAxisCell_subset_innerHalf (d : ℕ) (R : TriadicCube d) {mm : ℤ}
    {N : ℕ} (hN : 1 ≤ N) (hmm : R.scale + (N : ℤ) = mm) :
    openCubeSet R ⊆
      axisCubeInnerHalf (oneStepCenteredAxisCorner (cubeCenter R) mm)
        (cubeScaleFactor (originCube d mm)) := by
  subst hmm
  exact openCubeSet_subset_centeredParent_innerHalf R N hN

/-- The cell of a scale gap `N` sits in the fixed concentric interior of its
concentric parent as soon as `a ≤ N`. -/
theorem nfAxisCell_subset_concentric (d : ℕ) (R : TriadicCube d) {mm : ℤ}
    {a N : ℕ} (haN : a ≤ N) (hmm : R.scale + (N : ℤ) = mm) :
    openCubeSet R ⊆
      axisCube
        (CubeCalderonZygmund.axisCubeConcentricDepthCorner
          (oneStepCenteredAxisCorner (cubeCenter R) mm)
          (cubeScaleFactor (originCube d mm)) a)
        (CubeCalderonZygmund.axisCubeConcentricDepthSide
          (cubeScaleFactor (originCube d mm)) a) := by
  subst hmm
  exact openCubeSet_subset_centeredParent_concentricDepth R haN

/-- Nested-weight form of the axis harmonic prefactor. -/
theorem nfAxisHarmonic_prefactor_eq_nestedWeight
    (d : ℕ) (hd : 3 ≤ d) {source : ℤ} (N : ℕ) (R : TriadicCube d)
    (hscale : R.scale = source) (S : ℝ) :
    cubeScaleFactor R * (d : ℝ) ^ 2 *
        ((triadicAxisNormalizedMeasureRatio R
          (CubeCalderonZygmund.axisCubeConcentricDepthSide
            (cubeScaleFactor (originCube d (source + (N : ℤ))))
            (nfAxisHarmonicDepth d hd + 1))) ^
          (1 / (oneStepHarmonicExponent d hd).exponent).toReal).toReal *
        (nfAxisHarmonicConst d hd *
          (cubeScaleFactor (originCube d (source + (N : ℤ))))⁻¹ * S) =
      ((d : ℝ) ^ 2 * nfAxisHarmonicConst d hd) *
        oneStepNestedHarmonicWeight d hd (nfAxisHarmonicDepth d hd) N * S := by
  rw [triadicAxisNormalizedMeasureRatio_nested_eq N
    (nfAxisHarmonicDepth d hd) R hscale]
  rw [oneStepNested_harmonic_prefactor_eq (source := source) N R hscale
    (((ENNReal.ofReal
      (((3 : ℝ) ^ ((N : ℤ) - ((nfAxisHarmonicDepth d hd + 1 : ℕ) : ℤ))) ^ d)) ^
        (1 / (oneStepHarmonicExponent d hd).exponent).toReal).toReal)
    (nfAxisHarmonicConst d hd) S]
  unfold oneStepNestedHarmonicWeight
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily
