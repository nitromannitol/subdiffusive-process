module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold.InnerHalfFamilyAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold.NestedCellsAreSourceCells

@[expose] public section

/-!
# The shared-parent nested family with all three budgets

Exact mirror of `exists_nfNestedTwoRadiusFamily_allBudgets`
(`Section5NeumannFamily/NestedFamilyComplete.lean`) at the **Calderón--Zygmund
interior depth `a = 1`** instead of `a = nfAxisHarmonicDepth d hd + 1`.

With `a = 1` the cells of a retained overlap centre `S` (of scale `mm - 1`)
are *all* of its depth-`(N - 1)` descendants — every source-scale cell inside
`S`, not just those in the fixed concentric interior of the parent.  Three
consequences:

* the Dirichlet member's descendant average is inflated only by the
  **dimension-only** factor `3 ^ d` (against `(3 ^ d) ^ (depth + 1)` before);
* the coverage deficit `(3 ^ d) ^ (a - 1)` of
  `nfNestedIndex_card_mul_le_descendantsAtDepth_card` becomes `1`;
* the two harmonic estimates can no longer use the fixed concentric interior,
  so they route through the `a`-free
  `nfAxisHarmonic_innerHalf_cell_hessian`, at the auxiliary radius `N - 1` and
  with the dimension-only price `((3 : ℝ) ^ d) ^ (1/2)` absorbed into
  `nfInnerHalfHarmonicConst`.
-/

open MeasureTheory Homogenization
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily

noncomputable section

variable {d : ℕ}

/-- Index of the shared-parent nested family: a retained overlap centre
together with a depth-`(N - 1)` descendant of the origin cube one scale below
the parent. -/
abbrev NFInnerHalfIndex (d : ℕ) (K : ℤ) (j N : ℕ) :=
  NFNestedIndex d K j (originCube d ((K - (j : ℤ)) - ((1 : ℕ) : ℤ))) (N - 1)

/-- **The shared-parent nested two-radius Neumann Hessian family.**  The
Dirichlet member's descendant average is inflated only by `3 ^ d`, and both
harmonic radii are controlled at the auxiliary radius `N - 1`. -/
theorem exists_nfInnerHalfTwoRadiusFamily_allBudgets
    (d : ℕ) [NeZero d] (hd : 3 ≤ d) :
    ∃ C₁ C₂ : ℝ≥0∞, C₁ ≠ ∞ ∧ C₂ ≠ ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d)
        (K : ℤ) (j N : ℕ) (hh : 0 < h)
        (_hN : nfAxisHarmonicDepth d hd + 2 ≤ N)
        (_hp : vecNormSq p = 1) (_hblock : (h : ℝ) ≤ M.delta⁻¹)
        (V : NFSample d → CubeVectorW1pFunction
          (originCube d (K - (j : ℤ))) oneStepFourExponent)
        (hV : ∀ omega, (V omega).toField =
          (oneStepOriginDirichletSolution M n h p (K - (j : ℤ)) omega hh
            ).toH1Function.grad)
        (CD : ℝ≥0∞)
        (_hDbudget : ∫⁻ omega, ENNReal.ofReal
            (descendantsAverage (originCube d (K - (j : ℤ))) N
              (fun R => nfOriginCellB M n h p (K - (j : ℤ)) hh N V hV R omega ^
                (4 : ℕ))) ∂M.P.toMeasure ≤ CD),
        ∃ F : OneStepTwoRadiusNeumannHessianFamily d
            (NFInnerHalfIndex d K j N) (NFSample d) Finset.univ
            (nfNestedCell N),
          (∀ q omega, (F.neumann q omega).grad =
            (oneStepOriginNeumannSolution M n h p K omega hh
              ).toH1Function.grad) ∧
          (∫⁻ omega,
              ((((Finset.univ : Finset (NFInnerHalfIndex d K j N)).card :
                  ℝ≥0∞))⁻¹ *
                ∑ q : NFInnerHalfIndex d K j N, ENNReal.ofReal
                  (F.toCellFamily.dirichlet q omega ^ (4 : ℕ)))
              ∂M.P.toMeasure ≤
            (((3 ^ d : ℕ)) : ℝ≥0∞) * CD) ∧
          (∫⁻ omega,
              ((((Finset.univ : Finset (NFInnerHalfIndex d K j N)).card :
                  ℝ≥0∞))⁻¹ *
                ∑ q : NFInnerHalfIndex d K j N, ENNReal.ofReal
                  (F.toCellFamily.localHarmonic q omega ^ (4 : ℕ)))
              ∂M.P.toMeasure ≤
            C₁ * oneStepNestedHarmonicFourthError
              (nfAxisHarmonicDepth d hd) (N - 1)) ∧
          (∫⁻ omega,
              ((((Finset.univ : Finset (NFInnerHalfIndex d K j N)).card :
                  ℝ≥0∞))⁻¹ *
                ∑ q : NFInnerHalfIndex d K j N, ENNReal.ofReal
                  (F.toCellFamily.outerHarmonic q omega ^ (4 : ℕ)))
              ∂M.P.toMeasure ≤
            C₂ * oneStepNestedHarmonicFourthError
              (nfAxisHarmonicDepth d hd) (N - 1)) := by
  classical
  obtain ⟨Couter, hCouterTop, houter⟩ :=
    exists_lintegral_oneStepNeumannOverlapRemainderCoordinateSum_four_le d
  set A : ℝ := nfInnerHalfHarmonicConst d hd with hAdef
  have hA0 : 0 ≤ A := nfInnerHalfHarmonicConst_nonneg d hd
  refine ⟨ENNReal.ofReal (A ^ (4 : ℕ)) *
      ENNReal.ofReal (16 * (d : ℝ) ^ (4 : ℕ) *
        oneStepSourceParentGradientConst ^ (4 : ℕ)),
    ENNReal.ofReal (A ^ (4 : ℕ)) * Couter,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt hCouterTop), ?_⟩
  intro M n h p K j N hh hN hp hblock V hV CD hDbudget
  have hak : 1 + (N - 1) = N := by omega
  have hone : 1 ≤ N := by omega
  -- geometry
  have hSscale : ∀ S : NFOverlapIndex d K j, (S.1).scale + 1 = (K - (j : ℤ)) := fun S =>
    nfOverlapCentre_scale S.2
  have hparS : ∀ S : NFOverlapIndex d K j,
      translateSet (cubeCenter S.1) (openCubeSet (originCube d (K - (j : ℤ)))) ⊆
        openCubeSet (originCube d K) := fun S =>
    (hSscale S) ▸ (oneStepOverlapParent_subset_outerCube S.2)
  have hRscale : ∀ q : NFInnerHalfIndex d K j N,
      (q.2.1).scale = (K - (j : ℤ)) - (N : ℤ) := by
    intro q
    have hq := scale_eq_sub_of_mem_descendantsAtDepth q.2.2
    simp only [originCube] at hq
    omega
  have hRmem : ∀ q : NFInnerHalfIndex d K j N,
      q.2.1 ∈ descendantsAtDepth (originCube d (K - (j : ℤ))) N := by
    intro q
    have hP₀mem : (originCube d ((K - (j : ℤ)) - ((1 : ℕ) : ℤ))) ∈ descendantsAtDepth (originCube d (K - (j : ℤ))) 1 := by
      rw [← centralDescendant_originCube d (K - (j : ℤ)) 1]
      exact CubeCalderonZygmund.centralDescendant_mem_descendantsAtDepth _ 1
    have := mem_descendantsAtDepth_trans hP₀mem q.2.2
    rwa [hak] at this
  have hscaleq : ∀ q : NFInnerHalfIndex d K j N,
      (nfNestedCell N q).scale + (N : ℤ) = (K - (j : ℤ)) := by
    intro q
    rw [nfNestedCell_scale, hRscale q]
    ring
  have hconc : ∀ q : NFInnerHalfIndex d K j N,
      openCubeSet (nfNestedCell N q) ⊆
        axisCube
          (CubeCalderonZygmund.axisCubeConcentricDepthCorner
            (oneStepCenteredAxisCorner (cubeCenter q.1.1) (K - (j : ℤ)))
            (cubeScaleFactor (originCube d (K - (j : ℤ)))) 1)
          (CubeCalderonZygmund.axisCubeConcentricDepthSide
            (cubeScaleFactor (originCube d (K - (j : ℤ)))) 1) := by
    intro q
    exact openCubeSet_nfNestedCell_subset_concentric hone hak
      (fun S => hSscale S) q
  have hcentre : ∀ q : NFInnerHalfIndex d K j N,
      cubeCenter (nfNestedCell N q) ∈
        oneStepCenteredParent (cubeCenter q.1.1) ((K - (j : ℤ)) - 1) := by
    intro q
    have hmem := hconc q (cubeCenter_mem_openCubeSet (nfNestedCell N q))
    rw [nfAxisConcentric_eq_translate d (cubeCenter q.1.1) (K - (j : ℤ)) 1] at hmem
    exact hmem
  -- the family
  obtain ⟨F, hneu, hdir, hlocW, houtW⟩ :=
    exists_nfAxisInnerHalfNeumannHessianFamily hd M n h p K (K - (j : ℤ)) N hN hh
      (Finset.univ : Finset (NFInnerHalfIndex d K j N)) (nfNestedCell N)
      (fun q => cubeCenter q.1.1) hscaleq (fun q => hparS q.1) hcentre
  refine ⟨F, hneu, ?_, ?_, ?_⟩
  · -- Dirichlet budget
    haveI hne₂ : Nonempty {R₀ : TriadicCube d //
        R₀ ∈ descendantsAtDepth (originCube d ((K - (j : ℤ)) - ((1 : ℕ) : ℤ))) (N - 1)} := by
      obtain ⟨R₀, hR₀⟩ := descendantsAtDepth_nonempty (originCube d ((K - (j : ℤ)) - ((1 : ℕ) : ℤ))) (N - 1)
      exact ⟨⟨R₀, hR₀⟩⟩
    set Bf : TriadicCube d → NFSample d → ℝ :=
      nfOriginCellB M n h p (K - (j : ℤ)) hh N V hV with hBfdef
    have hne₁ : (Finset.univ : Finset (NFOverlapIndex d K j)).Nonempty := by
      obtain ⟨S, hS⟩ := overlapCentersAtDepth_nonempty (originCube d K) j
      exact ⟨⟨S, hS⟩, Finset.mem_univ _⟩
    have hmeasB : ∀ R : TriadicCube d, Measurable (Bf R) := fun R =>
      measurable_nfOriginCellB M n h p (K - (j : ℤ)) hh N V hV R
    have hBD : ∀ (q : NFInnerHalfIndex d K j N) (omega : NFSample d),
        F.toCellFamily.dirichlet q omega =
          Bf q.2.1
            (translatePotentialSequence (cubeCenter q.1.1) omega) := by
      intro q omega
      rw [toCellFamily_dirichlet_eq]
      exact nfNested_dirichletB_eq M n h p K (K - (j : ℤ)) j N hh hone V hV q
        (hSscale q.1) (hRscale q) (hRmem q) omega
        (F.dirichletHessian q omega) (hdir q omega)
    set c₁ : ℝ≥0∞ := ((Finset.univ : Finset (NFOverlapIndex d K j)).card :
      ℝ≥0∞) with hc₁def
    set c₂ : ℝ≥0∞ := ((Finset.univ : Finset {R₀ : TriadicCube d //
      R₀ ∈ descendantsAtDepth (originCube d ((K - (j : ℤ)) - ((1 : ℕ) : ℤ))) (N - 1)}).card : ℝ≥0∞) with hc₂def
    have hc₂ne : c₂ ≠ 0 := by
      rw [hc₂def]
      simpa using Finset.card_ne_zero_of_mem
        (Finset.mem_univ (Classical.arbitrary
          {R₀ : TriadicCube d // R₀ ∈ descendantsAtDepth (originCube d ((K - (j : ℤ)) - ((1 : ℕ) : ℤ))) (N - 1)}))
    have hc₂top : c₂ ≠ ∞ := by rw [hc₂def]; finiteness
    have hmeasInner : ∀ R₀ : {R₀ : TriadicCube d //
        R₀ ∈ descendantsAtDepth (originCube d ((K - (j : ℤ)) - ((1 : ℕ) : ℤ))) (N - 1)},
        Measurable (fun omega : NFSample d => c₂⁻¹ * (c₁⁻¹ *
          ∑ S : NFOverlapIndex d K j, ENNReal.ofReal
            (Bf R₀.1
              (translatePotentialSequence (cubeCenter S.1) omega) ^
                (4 : ℕ)))) := by
      intro R₀
      refine measurable_const.mul (measurable_const.mul ?_)
      refine Finset.measurable_sum _ fun S _ => ?_
      exact (((hmeasB R₀.1).comp
        (measurable_translatePotentialSequence (cubeCenter S.1))).pow_const
          4).ennreal_ofReal
    have hmeasOuter : ∀ R₀ : {R₀ : TriadicCube d //
        R₀ ∈ descendantsAtDepth (originCube d ((K - (j : ℤ)) - ((1 : ℕ) : ℤ))) (N - 1)},
        Measurable (fun omega : NFSample d => ENNReal.ofReal
          (Bf R₀.1 omega ^ (4 : ℕ))) :=
      fun R₀ => ((hmeasB R₀.1).pow_const 4).ennreal_ofReal
    have hsubfam : descendantsAtDepth (originCube d ((K - (j : ℤ)) - ((1 : ℕ) : ℤ))) (N - 1) ⊆
        descendantsAtDepth (originCube d (K - (j : ℤ))) N := by
      intro R hR
      have hP₀mem : (originCube d ((K - (j : ℤ)) - ((1 : ℕ) : ℤ))) ∈ descendantsAtDepth (originCube d (K - (j : ℤ))) 1 := by
        rw [← centralDescendant_originCube d (K - (j : ℤ)) 1]
        exact CubeCalderonZygmund.centralDescendant_mem_descendantsAtDepth _ 1
      have := mem_descendantsAtDepth_trans hP₀mem hR
      rwa [hak] at this
    have hstep1 : ∀ omega : NFSample d,
        ((Finset.univ : Finset (NFInnerHalfIndex d K j N)).card : ℝ≥0∞)⁻¹ *
            ∑ q : NFInnerHalfIndex d K j N, ENNReal.ofReal
              (F.toCellFamily.dirichlet q omega ^ (4 : ℕ)) =
          ∑ R₀ : {R₀ : TriadicCube d // R₀ ∈ descendantsAtDepth (originCube d ((K - (j : ℤ)) - ((1 : ℕ) : ℤ))) (N - 1)},
            c₂⁻¹ * (c₁⁻¹ *
              ∑ S : NFOverlapIndex d K j, ENNReal.ofReal
                (Bf R₀.1
                  (translatePotentialSequence (cubeCenter S.1) omega) ^
                    (4 : ℕ))) := by
      intro omega
      have hswap := nfProd_average_swap
        (ι₁ := NFOverlapIndex d K j)
        (ι₂ := {R₀ : TriadicCube d // R₀ ∈ descendantsAtDepth (originCube d ((K - (j : ℤ)) - ((1 : ℕ) : ℤ))) (N - 1)})
        (fun S R₀ => ENNReal.ofReal
          (Bf R₀.1
            (translatePotentialSequence (cubeCenter S.1) omega) ^ (4 : ℕ)))
      refine Eq.trans ?_ hswap
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hBD q omega]
    calc
      ∫⁻ omega, (((Finset.univ :
              Finset (NFInnerHalfIndex d K j N)).card : ℝ≥0∞)⁻¹ *
            ∑ q : NFInnerHalfIndex d K j N, ENNReal.ofReal
              (F.toCellFamily.dirichlet q omega ^ (4 : ℕ)))
          ∂M.P.toMeasure
        = ∫⁻ omega, (∑ R₀ : {R₀ : TriadicCube d //
              R₀ ∈ descendantsAtDepth (originCube d ((K - (j : ℤ)) - ((1 : ℕ) : ℤ))) (N - 1)}, c₂⁻¹ * (c₁⁻¹ *
              ∑ S : NFOverlapIndex d K j, ENNReal.ofReal
                (Bf R₀.1
                  (translatePotentialSequence (cubeCenter S.1) omega) ^
                    (4 : ℕ)))) ∂M.P.toMeasure := lintegral_congr hstep1
      _ = ∑ R₀ : {R₀ : TriadicCube d // R₀ ∈ descendantsAtDepth (originCube d ((K - (j : ℤ)) - ((1 : ℕ) : ℤ))) (N - 1)},
            ∫⁻ omega, (c₂⁻¹ * (c₁⁻¹ *
              ∑ S : NFOverlapIndex d K j, ENNReal.ofReal
                (Bf R₀.1
                  (translatePotentialSequence (cubeCenter S.1) omega) ^
                    (4 : ℕ)))) ∂M.P.toMeasure :=
          lintegral_finset_sum _ (fun R₀ _ => hmeasInner R₀)
      _ = ∑ R₀ : {R₀ : TriadicCube d // R₀ ∈ descendantsAtDepth (originCube d ((K - (j : ℤ)) - ((1 : ℕ) : ℤ))) (N - 1)},
            c₂⁻¹ * ∫⁻ omega, (c₁⁻¹ *
              ∑ S : NFOverlapIndex d K j, ENNReal.ofReal
                (Bf R₀.1
                  (translatePotentialSequence (cubeCenter S.1) omega) ^
                    (4 : ℕ))) ∂M.P.toMeasure := by
          refine Finset.sum_congr rfl fun R₀ _ => ?_
          exact lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hc₂ne)
      _ = ∑ R₀ : {R₀ : TriadicCube d // R₀ ∈ descendantsAtDepth (originCube d ((K - (j : ℤ)) - ((1 : ℕ) : ℤ))) (N - 1)},
            c₂⁻¹ * ∫⁻ omega, ENNReal.ofReal
              (Bf R₀.1 omega ^ (4 : ℕ))
              ∂M.P.toMeasure := by
          refine Finset.sum_congr rfl fun R₀ _ => ?_
          congr 1
          exact lintegral_average_comp_translatePotentialSequence_four_eq
            M (fun S : NFOverlapIndex d K j => cubeCenter S.1) Finset.univ
            hne₁ _ (hmeasB R₀.1)
      _ = c₂⁻¹ * ∑ R₀ : {R₀ : TriadicCube d //
            R₀ ∈ descendantsAtDepth (originCube d ((K - (j : ℤ)) - ((1 : ℕ) : ℤ))) (N - 1)},
            ∫⁻ omega, ENNReal.ofReal
              (Bf R₀.1 omega ^ (4 : ℕ))
              ∂M.P.toMeasure := (Finset.mul_sum _ _ _).symm
      _ = c₂⁻¹ * ∫⁻ omega, (∑ R₀ : {R₀ : TriadicCube d //
            R₀ ∈ descendantsAtDepth (originCube d ((K - (j : ℤ)) - ((1 : ℕ) : ℤ))) (N - 1)}, ENNReal.ofReal
              (Bf R₀.1 omega ^ (4 : ℕ)))
              ∂M.P.toMeasure := by
          congr 1
          exact (lintegral_finset_sum _ (fun R₀ _ => hmeasOuter R₀)).symm
      _ = c₂⁻¹ * ∫⁻ omega, (∑ R ∈ descendantsAtDepth (originCube d ((K - (j : ℤ)) - ((1 : ℕ) : ℤ))) (N - 1), ENNReal.ofReal
              (Bf R omega ^ (4 : ℕ)))
              ∂M.P.toMeasure := by
          congr 1
          refine lintegral_congr fun omega => ?_
          exact Finset.sum_coe_sort (descendantsAtDepth (originCube d ((K - (j : ℤ)) - ((1 : ℕ) : ℤ))) (N - 1))
            (fun R => ENNReal.ofReal (Bf R omega ^ (4 : ℕ)))
      _ ≤ c₂⁻¹ * ∫⁻ omega, (∑ R ∈ descendantsAtDepth (originCube d (K - (j : ℤ))) N,
              ENNReal.ofReal
              (Bf R omega ^ (4 : ℕ)))
              ∂M.P.toMeasure := by
          refine mul_le_mul' le_rfl (lintegral_mono fun omega => ?_)
          exact Finset.sum_le_sum_of_subset hsubfam
      _ = c₂⁻¹ * ∫⁻ omega,
            (((descendantsAtDepth (originCube d (K - (j : ℤ))) N).card : ℝ≥0∞) *
              ENNReal.ofReal (descendantsAverage (originCube d (K - (j : ℤ))) N
                (fun R => Bf R omega ^
                  (4 : ℕ)))) ∂M.P.toMeasure := by
          congr 1
          refine lintegral_congr fun omega => ?_
          exact nfDescendantsAverage_ofReal (originCube d (K - (j : ℤ))) N _
            (fun R => pow_nonneg (nfOriginCellB_nonneg M n h p (K - (j : ℤ)) hh N V hV R
              omega) 4)
      _ = c₂⁻¹ * ((descendantsAtDepth (originCube d (K - (j : ℤ))) N).card : ℝ≥0∞) *
            ∫⁻ omega, ENNReal.ofReal
              (descendantsAverage (originCube d (K - (j : ℤ))) N
                (fun R => Bf R omega ^
                  (4 : ℕ))) ∂M.P.toMeasure := by
          rw [mul_assoc]
          congr 1
          exact lintegral_const_mul' _ _ (by finiteness)
      _ ≤ c₂⁻¹ * ((descendantsAtDepth (originCube d (K - (j : ℤ))) N).card : ℝ≥0∞) *
            CD := by gcongr
      _ = (((3 ^ d : ℕ)) : ℝ≥0∞) * CD := by
          congr 1
          have hcard₂ : c₂ = (((3 ^ d) ^ (N - 1) : ℕ) : ℝ≥0∞) := by
            rw [hc₂def, Finset.card_univ, Fintype.card_coe,
              descendantsAtDepth_card]
          have hcardN : ((descendantsAtDepth (originCube d (K - (j : ℤ))) N).card :
              ℝ≥0∞) = (((3 ^ d) ^ N : ℕ) : ℝ≥0∞) := by
            rw [descendantsAtDepth_card]
          have hsplit : ((3 ^ d) ^ N : ℕ) =
              ((3 ^ d : ℕ)) * ((3 ^ d) ^ (N - 1) : ℕ) := by
            rw [← pow_succ']
            congr 1
            omega
          rw [hcard₂, hcardN, hsplit]
          push_cast
          rw [mul_comm ((3 : ℝ≥0∞) ^ d) ((((3 : ℝ≥0∞)) ^ d) ^ (N - 1)),
            ← mul_assoc, ENNReal.inv_mul_cancel (by positivity)
              (by finiteness), one_mul]
  · -- local harmonic budget
    refine lintegral_average_nestedHarmonic_four_le hd (by omega : _ + 1 ≤ N - 1)
      M.P.toMeasure Finset.univ A hA0
      (fun q omega => F.toCellFamily.localHarmonic q omega)
      (fun q omega => oneStepNeumannDirichletAxisCoordinateSum M n h p
        (cubeCenter q.1.1) (K - (j : ℤ)) omega hh)
      (fun q hq omega => F.toCellFamily.localHarmonic_nonneg q hq omega)
      (fun q _hq omega => hlocW q omega) ?_
    refine lintegral_nfProd_localReadout_four_le M n h p ?_
      (fun q : NFInnerHalfIndex d K j N => cubeCenter q.1.1) (K - (j : ℤ)) hh hp hblock
    obtain ⟨S, hS⟩ := overlapCentersAtDepth_nonempty (originCube d K) j
    obtain ⟨R₀, hR₀⟩ := descendantsAtDepth_nonempty (originCube d ((K - (j : ℤ)) - ((1 : ℕ) : ℤ))) (N - 1)
    exact ⟨(⟨S, hS⟩, ⟨R₀, hR₀⟩), Finset.mem_univ _⟩
  · -- outer harmonic budget
    haveI hne₂ : Nonempty {R₀ : TriadicCube d //
        R₀ ∈ descendantsAtDepth (originCube d ((K - (j : ℤ)) - ((1 : ℕ) : ℤ))) (N - 1)} := by
      obtain ⟨R₀, hR₀⟩ := descendantsAtDepth_nonempty (originCube d ((K - (j : ℤ)) - ((1 : ℕ) : ℤ))) (N - 1)
      exact ⟨⟨R₀, hR₀⟩⟩
    refine lintegral_average_nestedHarmonic_four_le hd (by omega : _ + 1 ≤ N - 1)
      M.P.toMeasure Finset.univ A hA0
      (fun q omega => F.toCellFamily.outerHarmonic q omega)
      (fun q omega => nfAxisOuterCoordinateSum M n h omega p
        (cubeCenter q.1.1) K (K - (j : ℤ)) (hparS q.1) hh)
      (fun q hq omega => F.toCellFamily.outerHarmonic_nonneg q hq omega)
      (fun q _hq omega => houtW q omega) ?_
    have hcollapse : ∀ omega : NFSample d,
        ((Finset.univ : Finset (NFInnerHalfIndex d K j N)).card : ℝ≥0∞)⁻¹ *
            ∑ q : NFInnerHalfIndex d K j N, ENNReal.ofReal
              (nfAxisOuterCoordinateSum M n h omega p (cubeCenter q.1.1) K (K - (j : ℤ))
                (hparS q.1) hh ^ (4 : ℕ)) =
          (((overlapCentersAtDepth (originCube d K) j).card : ℝ≥0∞))⁻¹ *
            ∑ S ∈ overlapCentersAtDepth (originCube d K) j, ENNReal.ofReal
              (oneStepNeumannOverlapRemainderCoordinateSum M n h p K j S
                omega hh ^ (4 : ℕ)) := by
      intro omega
      have hprod := nfProd_average_eq
        (ι₁ := NFOverlapIndex d K j)
        (ι₂ := {R₀ : TriadicCube d // R₀ ∈ descendantsAtDepth (originCube d ((K - (j : ℤ)) - ((1 : ℕ) : ℤ))) (N - 1)})
        (fun S => ENNReal.ofReal
          (nfAxisOuterCoordinateSum M n h omega p (cubeCenter S.1) K (K - (j : ℤ))
            (hparS S) hh ^ (4 : ℕ)))
      rw [hprod]
      have hcard : ((Finset.univ : Finset (NFOverlapIndex d K j)).card :
          ℝ≥0∞) = ((overlapCentersAtDepth (originCube d K) j).card : ℝ≥0∞) := by
        simp
      rw [hcard]
      congr 1
      rw [← Finset.sum_coe_sort (overlapCentersAtDepth (originCube d K) j)
        (fun S => ENNReal.ofReal
          (oneStepNeumannOverlapRemainderCoordinateSum M n h p K j S
            omega hh ^ (4 : ℕ)))]
      refine Finset.sum_congr rfl fun S _ => ?_
      congr 2
      rw [nfAxisOuterCoordinateSum_congr_scale M n h omega p (cubeCenter S.1)
        K (K - (j : ℤ)) ((S.1).scale + 1) (hSscale S).symm (hparS S)
        (oneStepOverlapParent_subset_outerCube S.2) hh]
      exact nfAxisOuterCoordinateSum_eq_overlap M n h omega p K j S.1 S.2 hh
    calc
      _ = ∫⁻ omega, ((((overlapCentersAtDepth (originCube d K) j).card :
              ℝ≥0∞))⁻¹ *
            ∑ S ∈ overlapCentersAtDepth (originCube d K) j, ENNReal.ofReal
              (oneStepNeumannOverlapRemainderCoordinateSum M n h p K j S
                omega hh ^ (4 : ℕ))) ∂M.P.toMeasure :=
        lintegral_congr hcollapse
      _ ≤ Couter := houter M n h p K j hh hp hblock

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold
