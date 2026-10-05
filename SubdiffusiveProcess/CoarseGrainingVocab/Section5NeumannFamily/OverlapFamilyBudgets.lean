module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily.AxisFamilyAssembly

@[expose] public section




open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily

open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-! ## The concentric shrunken cell -/

/-- The triadic cube concentric with `S`, `N - 1` scales below `S`.  Its
scale gap to the overlap parent of `S` is exactly `N`. -/
def nfShrinkCell (S : TriadicCube d) (N : ℕ) : TriadicCube d where
  scale := S.scale + 1 - (N : ℤ)
  index := fun i => S.index i * 3 ^ (N - 1)

@[simp] theorem nfShrinkCell_scale (S : TriadicCube d) (N : ℕ) :
    (nfShrinkCell S N).scale = S.scale + 1 - (N : ℤ) := rfl

theorem nfShrinkCell_scale_add (S : TriadicCube d) (N : ℕ) :
    (nfShrinkCell S N).scale + (N : ℤ) = S.scale + 1 := by
  simp only [nfShrinkCell_scale]
  ring

theorem cubeCenter_nfShrinkCell (S : TriadicCube d) {N : ℕ} (hN : 1 ≤ N) :
    cubeCenter (nfShrinkCell S N) = cubeCenter S := by
  funext i
  have hthree : (3 : ℝ) ≠ 0 := by norm_num
  have hexp : (((N - 1 : ℕ) : ℤ)) + (S.scale + 1 - (N : ℤ)) = S.scale := by
    omega
  simp only [cubeCenter, cubeScaleFactor, nfShrinkCell]
  push_cast
  rw [← zpow_natCast (3 : ℝ) (N - 1), mul_assoc, ← zpow_add₀ hthree, hexp]

theorem nfShrinkCell_subset_innerHalf (d : ℕ) (S : TriadicCube d) {N : ℕ}
    (hN : 1 ≤ N) :
    openCubeSet (nfShrinkCell S N) ⊆
      axisCubeInnerHalf
        (oneStepCenteredAxisCorner (cubeCenter S) (S.scale + 1))
        (cubeScaleFactor (originCube d (S.scale + 1))) := by
  have hbase := nfAxisCell_subset_innerHalf d (nfShrinkCell S N) hN
    (nfShrinkCell_scale_add S N)
  rwa [cubeCenter_nfShrinkCell S hN] at hbase

theorem nfShrinkCell_subset_concentric (d : ℕ) (S : TriadicCube d) {a N : ℕ}
    (hN : 1 ≤ N) (haN : a ≤ N) :
    openCubeSet (nfShrinkCell S N) ⊆
      axisCube
        (CubeCalderonZygmund.axisCubeConcentricDepthCorner
          (oneStepCenteredAxisCorner (cubeCenter S) (S.scale + 1))
          (cubeScaleFactor (originCube d (S.scale + 1))) a)
        (CubeCalderonZygmund.axisCubeConcentricDepthSide
          (cubeScaleFactor (originCube d (S.scale + 1))) a) := by
  have hbase := nfAxisCell_subset_concentric d (nfShrinkCell S N) haN
    (nfShrinkCell_scale_add S N)
  rwa [cubeCenter_nfShrinkCell S hN] at hbase




theorem nfAxisOuterCoordinateSum_eq_overlap [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : NFSample d) (p : Vec d) (K : ℤ) (j : ℕ) (S : TriadicCube d)
    (hS : S ∈ overlapCentersAtDepth (originCube d K) j) (hh : 0 < h) :
    nfAxisOuterCoordinateSum M n h omega p (cubeCenter S) K (S.scale + 1)
        (oneStepOverlapParent_subset_outerCube hS) hh =
      oneStepNeumannOverlapRemainderCoordinateSum M n h p K j S omega hh := by
  rw [oneStepNeumannOverlapRemainderCoordinateSum, dite_eq_left hS]
  rfl

/-- Every retained overlap centre has scale `K - (j+1)`, so its overlap
parent has scale `K - j`. -/
theorem nfOverlapCentre_scale {K : ℤ} {j : ℕ} {S : TriadicCube d}
    (hS : S ∈ overlapCentersAtDepth (originCube d K) j) :
    S.scale + 1 = K - (j : ℤ) := by
  have hdesc := mem_descendantsAtDepth_of_mem_overlapCentersAtDepth hS
  have hscale := scale_eq_sub_of_mem_descendantsAtDepth hdesc
  simp only [originCube] at hscale
  omega

/-- The outer readout does not depend on how the parent scale is presented. -/
theorem nfAxisOuterCoordinateSum_congr_scale [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : NFSample d) (p z : Vec d) (K m m' : ℤ) (hm : m = m')
    (hsub : translateSet z (openCubeSet (originCube d m)) ⊆
      openCubeSet (originCube d K))
    (hsub' : translateSet z (openCubeSet (originCube d m')) ⊆
      openCubeSet (originCube d K)) (hh : 0 < h) :
    nfAxisOuterCoordinateSum M n h omega p z K m hsub hh =
      nfAxisOuterCoordinateSum M n h omega p z K m' hsub' hh := by
  subst hm
  rfl

/-! ## The overlap index -/

/-- Index type of the retained overlap family. -/
abbrev NFOverlapIndex (d : ℕ) (K : ℤ) (j : ℕ) :=
  {S : TriadicCube d // S ∈ overlapCentersAtDepth (originCube d K) j}

/-- The two-radius Neumann Hessian family on the retained overlap centres,
with the two harmonic fourth-moment budgets in exactly the shape consumed by
`twoRadiusNeumannHessian_nested_thermodynamic_readout_le`. -/
theorem exists_nfOverlapTwoRadiusFamily_harmonicBudgets
    (d : ℕ) [NeZero d] (hd : 3 ≤ d) :
    ∃ C₁ C₂ : ℝ≥0∞, C₁ ≠ ∞ ∧ C₂ ≠ ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
        (K : ℤ) (j N : ℕ) (hh : 0 < h)
        (_hN : nfAxisHarmonicDepth d hd + 1 ≤ N)
        (_hp : vecNormSq p = 1) (_hblock : (h : ℝ) ≤ M.delta⁻¹),
        ∃ (cell : NFOverlapIndex d K j → TriadicCube d)
          (F : OneStepTwoRadiusNeumannHessianFamily d
              (NFOverlapIndex d K j) (NFSample d) Finset.univ cell),
          (∀ i omega, (F.neumann i omega).grad =
            (oneStepOriginNeumannSolution M n h p K omega hh
              ).toH1Function.grad) ∧
          (∫⁻ omega, ((((Finset.univ :
                  Finset (NFOverlapIndex d K j)).card : ℝ≥0∞)⁻¹) *
                ∑ i : NFOverlapIndex d K j, ENNReal.ofReal
                  (F.toCellFamily.localHarmonic i omega ^ (4 : ℕ)))
              ∂M.P.toMeasure ≤
            C₁ * oneStepNestedHarmonicFourthError
              (nfAxisHarmonicDepth d hd) N) ∧
          (∫⁻ omega, ((((Finset.univ :
                  Finset (NFOverlapIndex d K j)).card : ℝ≥0∞)⁻¹) *
                ∑ i : NFOverlapIndex d K j, ENNReal.ofReal
                  (F.toCellFamily.outerHarmonic i omega ^ (4 : ℕ)))
              ∂M.P.toMeasure ≤
            C₂ * oneStepNestedHarmonicFourthError
              (nfAxisHarmonicDepth d hd) N) := by
  classical
  obtain ⟨Couter, hCouterTop, houter⟩ :=
    exists_lintegral_oneStepNeumannOverlapRemainderCoordinateSum_four_le d
  set A : ℝ := (d : ℝ) ^ 2 * nfAxisHarmonicConst d hd with hA
  have hA0 : 0 ≤ A :=
    mul_nonneg (by positivity) (nfAxisHarmonicConst_pos d hd).le
  set Clocal : ℝ≥0∞ := ENNReal.ofReal (16 * (d : ℝ) ^ (4 : ℕ) *
    oneStepSourceParentGradientConst ^ (4 : ℕ)) with hClocal
  refine ⟨ENNReal.ofReal (A ^ (4 : ℕ)) * Clocal,
    ENNReal.ofReal (A ^ (4 : ℕ)) * Couter,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt hCouterTop), ?_⟩
  intro M n h p K j N hh hN hp hblock
  set mm : ℤ := K - (j : ℤ) with hmm
  have hone : 1 ≤ N := le_trans (Nat.le_add_left 1 _) hN
  have hsc : ∀ i : NFOverlapIndex d K j, (i.1).scale + 1 = mm := fun i =>
    nfOverlapCentre_scale i.2
  have hpar : ∀ i : NFOverlapIndex d K j,
      translateSet (cubeCenter i.1) (openCubeSet (originCube d mm)) ⊆
        openCubeSet (originCube d K) := fun i =>
    (hsc i) ▸ (oneStepOverlapParent_subset_outerCube i.2)
  have hhalf : ∀ i : NFOverlapIndex d K j,
      openCubeSet (nfShrinkCell i.1 N) ⊆
        axisCubeInnerHalf (oneStepCenteredAxisCorner (cubeCenter i.1) mm)
          (cubeScaleFactor (originCube d mm)) := fun i =>
    (hsc i) ▸ (nfShrinkCell_subset_innerHalf d i.1 hone)
  have hinner : ∀ i : NFOverlapIndex d K j,
      openCubeSet (nfShrinkCell i.1 N) ⊆
        axisCube
          (CubeCalderonZygmund.axisCubeConcentricDepthCorner
            (oneStepCenteredAxisCorner (cubeCenter i.1) mm)
            (cubeScaleFactor (originCube d mm))
            (nfAxisHarmonicDepth d hd + 1))
          (CubeCalderonZygmund.axisCubeConcentricDepthSide
            (cubeScaleFactor (originCube d mm))
            (nfAxisHarmonicDepth d hd + 1)) := fun i =>
    (hsc i) ▸ (nfShrinkCell_subset_concentric d i.1 hone hN)
  have hscale : ∀ i : NFOverlapIndex d K j,
      (nfShrinkCell i.1 N).scale + (N : ℤ) = mm := fun i => by
    rw [nfShrinkCell_scale_add]
    exact hsc i
  obtain ⟨F, hneu, _hdir, hlocW, houtW⟩ :=
    exists_nfAxisTwoRadiusNeumannHessianFamily hd M n h p K mm N hh
      (Finset.univ : Finset (NFOverlapIndex d K j))
      (fun i => nfShrinkCell i.1 N) (fun i => cubeCenter i.1)
      hscale hpar hhalf hinner
  refine ⟨fun i => nfShrinkCell i.1 N, F, hneu, ?_, ?_⟩
  · -- local radius
    refine lintegral_average_nestedHarmonic_four_le hd hN M.P.toMeasure
      Finset.univ A hA0
      (fun i omega => F.toCellFamily.localHarmonic i omega)
      (fun i omega => oneStepNeumannDirichletAxisCoordinateSum M n h p
        (cubeCenter i.1) mm omega hh)
      (fun i hi omega => F.toCellFamily.localHarmonic_nonneg i hi omega)
      (fun i _hi omega => hlocW i omega) ?_
    have hne : (Finset.univ : Finset (NFOverlapIndex d K j)).Nonempty := by
      obtain ⟨S, hS⟩ := overlapCentersAtDepth_nonempty (originCube d K) j
      exact ⟨⟨S, hS⟩, Finset.mem_univ _⟩
    have hbase := lintegral_average_oneStepNeumannDirichletAxisHarmonicGain_four_le
      (ι := NFOverlapIndex d K j) M n h p (fun i => cubeCenter i.1)
      Finset.univ hne mm 0 hh hp hblock
    have hcongr : ∀ omega : NFSample d,
        ((Finset.univ : Finset (NFOverlapIndex d K j)).card : ℝ≥0∞)⁻¹ *
            ∑ i : NFOverlapIndex d K j, ENNReal.ofReal
              (oneStepNeumannDirichletAxisCoordinateSum M n h p
                (cubeCenter i.1) mm omega hh ^ (4 : ℕ)) =
          ((Finset.univ : Finset (NFOverlapIndex d K j)).card : ℝ≥0∞)⁻¹ *
            ∑ i : NFOverlapIndex d K j, ENNReal.ofReal
              (oneStepNeumannDirichletAxisHarmonicGain M n h p
                (cubeCenter i.1) mm 0 omega hh ^ (4 : ℕ)) := by
      intro omega
      congr 1
      refine Finset.sum_congr rfl fun i _hi => ?_
      congr 2
      unfold oneStepNeumannDirichletAxisHarmonicGain
      norm_num
    calc
      _ = ∫⁻ omega, (((Finset.univ :
              Finset (NFOverlapIndex d K j)).card : ℝ≥0∞)⁻¹ *
            ∑ i : NFOverlapIndex d K j, ENNReal.ofReal
              (oneStepNeumannDirichletAxisHarmonicGain M n h p
                (cubeCenter i.1) mm 0 omega hh ^ (4 : ℕ)))
          ∂M.P.toMeasure := lintegral_congr hcongr
      _ ≤ Clocal * ENNReal.ofReal (((3 : ℝ) ^ (-((0 : ℕ) : ℤ))) ^ (4 : ℕ)) :=
        hbase
      _ = Clocal := by norm_num
  · -- outer radius
    refine lintegral_average_nestedHarmonic_four_le hd hN M.P.toMeasure
      Finset.univ A hA0
      (fun i omega => F.toCellFamily.outerHarmonic i omega)
      (fun i omega => nfAxisOuterCoordinateSum M n h omega p
        (cubeCenter i.1) K mm (hpar i) hh)
      (fun i hi omega => F.toCellFamily.outerHarmonic_nonneg i hi omega)
      (fun i _hi omega => houtW i omega) ?_
    have hbase := houter M n h p K j hh hp hblock
    have hcongr : ∀ omega : NFSample d,
        ((Finset.univ : Finset (NFOverlapIndex d K j)).card : ℝ≥0∞)⁻¹ *
            ∑ i : NFOverlapIndex d K j, ENNReal.ofReal
              (nfAxisOuterCoordinateSum M n h omega p (cubeCenter i.1) K mm
                (hpar i) hh ^ (4 : ℕ)) =
          (((overlapCentersAtDepth (originCube d K) j).card : ℝ≥0∞)⁻¹) *
            ∑ S ∈ overlapCentersAtDepth (originCube d K) j, ENNReal.ofReal
              (oneStepNeumannOverlapRemainderCoordinateSum M n h p K j S
                omega hh ^ (4 : ℕ)) := by
      intro omega
      have hcard : ((Finset.univ :
          Finset (NFOverlapIndex d K j)).card : ℝ≥0∞) =
          ((overlapCentersAtDepth (originCube d K) j).card : ℝ≥0∞) := by
        simp
      rw [hcard]
      congr 1
      rw [← Finset.sum_coe_sort (overlapCentersAtDepth (originCube d K) j)
        (fun S => ENNReal.ofReal
          (oneStepNeumannOverlapRemainderCoordinateSum M n h p K j S
            omega hh ^ (4 : ℕ)))]
      refine Finset.sum_congr rfl fun i _hi => ?_
      congr 2
      rw [nfAxisOuterCoordinateSum_congr_scale M n h omega p (cubeCenter i.1)
        K mm ((i.1).scale + 1) (hsc i).symm (hpar i)
        (oneStepOverlapParent_subset_outerCube i.2) hh]
      exact nfAxisOuterCoordinateSum_eq_overlap M n h omega p K j i.1 i.2 hh
    calc
      _ = ∫⁻ omega, ((((overlapCentersAtDepth (originCube d K) j).card :
              ℝ≥0∞)⁻¹) *
            ∑ S ∈ overlapCentersAtDepth (originCube d K) j, ENNReal.ofReal
              (oneStepNeumannOverlapRemainderCoordinateSum M n h p K j S
                omega hh ^ (4 : ℕ)))
          ∂M.P.toMeasure := lintegral_congr hcongr
      _ ≤ Couter := hbase

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily
