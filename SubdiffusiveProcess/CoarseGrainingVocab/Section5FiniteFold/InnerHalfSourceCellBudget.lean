module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold.InnerHalfNestedFamily
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold.NeumannSourceCellBudget

@[expose] public section

/-!
# The finite-`K` `delta ^ 68` budget over the shared-parent family

Mirror of `exists_nfNeumannSourceCellB_lintegral_budget` for the shared-parent
family of `InnerHalfNestedFamily.lean`.  Two changes:

* the auxiliary radius is `N = nfFoldRadius (nfAxisHarmonicDepth d hd) M.delta
  + 1`, so that the *harmonic* radius `N - 1` is still past the fold radius;
* the Dirichlet inflation is the dimension-only `3 ^ d`.

In exchange, the family's cells are **all** depth-`(N - 1)` descendants of the
retained overlap centres, so the index is no longer short of the source-cell
set by the factor `(3 ^ d) ^ nfAxisHarmonicDepth d hd`.
-/

open MeasureTheory Homogenization
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily

noncomputable section

/-- **Finite-`K` source-cell fourth-moment budget for the literal Neumann cell
Hessian, over the shared-parent family.** -/
theorem exists_nfInnerHalfNeumannSourceCellB_lintegral_budget
    (d : ℕ) [NeZero d] (hd : 3 ≤ d) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h K : ℕ) (p : Vec d),
        vecNormSq p = 1 → ∀ hh : 0 < h, (h : ℝ) ≤ M.delta⁻¹ →
          16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n →
          oneStepLocalizationScale n M.delta +
              (nfFoldRadius (nfAxisHarmonicDepth d hd) M.delta + 1) ≤ K →
          ∃ (j N : ℕ) (F : OneStepTwoRadiusNeumannHessianFamily d
                (NFInnerHalfIndex d (K : ℤ) j N) (NFSample d)
                Finset.univ (nfNestedCell N)),
            N = nfFoldRadius (nfAxisHarmonicDepth d hd) M.delta + 1 ∧
            j + N = K - oneStepLocalizationScale n M.delta ∧
            (∀ q omega, (F.neumann q omega).grad =
              (oneStepOriginNeumannSolution M n h p (K : ℤ) omega
                hh).toH1Function.grad) ∧
            (∀ q : NFInnerHalfIndex d (K : ℤ) j N,
              nfNestedCell N q ∈ oneStepSourceCells d K n M.delta) ∧
            ∫⁻ omega, ((((oneStepSourceCells d K n M.delta).card : ℝ≥0∞))⁻¹ *
                ∑ R ∈ oneStepSourceCells d K n M.delta,
                  ENNReal.ofReal (nfExtendByZero (nfNestedCell N)
                    F.toCellFamily.neumann R omega ^ (4 : ℕ)))
                ∂M.P.toMeasure ≤
              C * ENNReal.ofReal (M.delta ^ (68 : ℕ)) := by
  classical
  obtain ⟨CD0, hCD0top, hDir⟩ :=
    exists_lintegral_nfOriginDirichlet_descendantCellB_source_le d
  obtain ⟨C₁, C₂, hC₁, hC₂, hfam⟩ :=
    exists_nfInnerHalfTwoRadiusFamily_allBudgets d hd
  refine ⟨64 * (((3 ^ d : ℕ) : ℝ≥0∞) * CD0 + C₁ + C₂), ?_, ?_⟩
  · exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
        ⟨ENNReal.mul_ne_top (by finiteness) hCD0top.ne, hC₁⟩, hC₂⟩)
  intro M n h K p hp hh hblock hsource hK
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ,
      N = nfFoldRadius (nfAxisHarmonicDepth d hd) M.delta + 1 := ⟨_, rfl⟩
  rw [← hNdef] at hK
  obtain ⟨j, hjdef⟩ : ∃ j : ℕ,
      j = K - (oneStepLocalizationScale n M.delta + N) := ⟨_, rfl⟩
  have hdelta0 : 0 < M.delta := M.shellPrefix.delta_pos
  have hdelta1 : M.delta ≤ 1 :=
    M.shellPrefix.delta_le_half.trans (by norm_num)
  have hfold : nfAxisHarmonicDepth d hd + 1 ≤
      nfFoldRadius (nfAxisHarmonicDepth d hd) M.delta :=
    le_nfFoldRadius_left _ _
  have hN : nfAxisHarmonicDepth d hd + 2 ≤ N := by omega
  have hKj : (K : ℤ) - (j : ℤ) =
      ((oneStepLocalizationScale n M.delta + N : ℕ) : ℤ) := by omega
  have hjN : j + N = K - oneStepLocalizationScale n M.delta := by omega
  -- the canonical descendant Dirichlet budget at the inner parent
  obtain ⟨V, hV, hDbudget0⟩ := hDir M n h N
    (oneStepLocalizationScale n M.delta + N) p hp hh hblock hsource rfl
  have hshape : ∀ (omega : NFSample d),
      (fun R : TriadicCube d ↦
        if hR : R ∈ descendantsAtDepth
            (originCube d ((oneStepLocalizationScale n M.delta + N : ℕ) : ℤ))
              N then
          (oneStepCellB R
            ((nfOriginDirichletHessianOf M n h p
              ((oneStepLocalizationScale n M.delta + N : ℕ) : ℤ) hh V hV
              omega).restrict (isOpen_openCubeSet R)
                (openCubeSet_subset_of_mem_descendantsAtDepth hR))) ^ (4 : ℕ)
        else 0) =
      (fun R : TriadicCube d ↦
        nfOriginCellB M n h p
          ((oneStepLocalizationScale n M.delta + N : ℕ) : ℤ) hh N V hV R
          omega ^ (4 : ℕ)) := by
    intro omega
    funext R
    by_cases hR : R ∈ descendantsAtDepth
      (originCube d ((oneStepLocalizationScale n M.delta + N : ℕ) : ℤ)) N
    · simp only [nfOriginCellB, dite_eq_left hR]
    · simp only [nfOriginCellB, dite_eq_right hR]
      norm_num
  have hDbudget : ∫⁻ omega, ENNReal.ofReal
      (descendantsAverage
        (originCube d ((oneStepLocalizationScale n M.delta + N : ℕ) : ℤ)) N
        (fun R ↦ nfOriginCellB M n h p
          ((oneStepLocalizationScale n M.delta + N : ℕ) : ℤ) hh N V hV R
          omega ^ (4 : ℕ))) ∂M.P.toMeasure ≤
      CD0 * ENNReal.ofReal (M.delta ^ (68 : ℕ)) := by
    refine le_trans (le_of_eq ?_) hDbudget0
    exact lintegral_congr fun omega ↦ by rw [hshape omega]
  -- the family, with the inner-parent scale generalized so that the index
  -- type can be rewritten
  have key : ∀ (m : ℤ), m = (K : ℤ) - (j : ℤ) →
      ∀ (V' : NFSample d → CubeVectorW1pFunction (originCube d m)
            oneStepFourExponent)
        (hV' : ∀ omega, (V' omega).toField =
          (oneStepOriginDirichletSolution M n h p m omega
            hh).toH1Function.grad)
        (CD : ℝ≥0∞),
        (∫⁻ omega, ENNReal.ofReal
            (descendantsAverage (originCube d m) N
              (fun R ↦ nfOriginCellB M n h p m hh N V' hV' R omega ^ (4 : ℕ)))
            ∂M.P.toMeasure ≤ CD) →
        ∃ F : OneStepTwoRadiusNeumannHessianFamily d
            (NFInnerHalfIndex d (K : ℤ) j N) (NFSample d) Finset.univ
            (nfNestedCell N),
          (∀ q omega, (F.neumann q omega).grad =
            (oneStepOriginNeumannSolution M n h p (K : ℤ) omega
              hh).toH1Function.grad) ∧
          (∫⁻ omega, ((((Finset.univ :
                Finset (NFInnerHalfIndex d (K : ℤ) j N)).card : ℝ≥0∞))⁻¹ *
              ∑ q : NFInnerHalfIndex d (K : ℤ) j N, ENNReal.ofReal
                (F.toCellFamily.dirichlet q omega ^ (4 : ℕ)))
              ∂M.P.toMeasure ≤
            (((3 ^ d : ℕ)) : ℝ≥0∞) * CD) ∧
          (∫⁻ omega, ((((Finset.univ :
                Finset (NFInnerHalfIndex d (K : ℤ) j N)).card : ℝ≥0∞))⁻¹ *
              ∑ q : NFInnerHalfIndex d (K : ℤ) j N, ENNReal.ofReal
                (F.toCellFamily.localHarmonic q omega ^ (4 : ℕ)))
              ∂M.P.toMeasure ≤
            C₁ * oneStepNestedHarmonicFourthError
              (nfAxisHarmonicDepth d hd) (N - 1)) ∧
          (∫⁻ omega, ((((Finset.univ :
                Finset (NFInnerHalfIndex d (K : ℤ) j N)).card : ℝ≥0∞))⁻¹ *
              ∑ q : NFInnerHalfIndex d (K : ℤ) j N, ENNReal.ofReal
                (F.toCellFamily.outerHarmonic q omega ^ (4 : ℕ)))
              ∂M.P.toMeasure ≤
            C₂ * oneStepNestedHarmonicFourthError
              (nfAxisHarmonicDepth d hd) (N - 1)) := by
    intro m hm
    subst hm
    exact hfam M n h p (K : ℤ) j N hh hN hp hblock
  obtain ⟨F, hneumann, hDfam, hH₁fam, hH₂fam⟩ :=
    key ((oneStepLocalizationScale n M.delta + N : ℕ) : ℤ) hKj.symm V hV
      (CD0 * ENNReal.ofReal (M.delta ^ (68 : ℕ))) hDbudget
  refine ⟨j, N, F, hNdef, hjN, hneumann, ?_, ?_⟩
  · intro q
    have hmem := nfNestedCell_mem_descendantsAtDepth
      (d := d) (K := (K : ℤ)) (j := j) (N := N) (a := 1) (k := N - 1)
      le_rfl (by omega) q
    rw [hjN] at hmem
    exact hmem
  -- the finite-radius fold
  have hpow : ENNReal.ofReal (M.delta ^ (68 : ℕ)) =
      (ENNReal.ofReal M.delta) ^ (68 : ℕ) :=
    ENNReal.ofReal_pow hdelta0.le 68
  have herr : oneStepNestedHarmonicFourthError
      (nfAxisHarmonicDepth d hd) (N - 1) ≤
      (ENNReal.ofReal M.delta) ^ (68 : ℕ) := by
    rw [← hpow]
    exact oneStepNestedHarmonicFourthError_le_ofReal_delta_pow_sixtyEight
      (nfAxisHarmonicDepth d hd) hdelta0 hdelta1 (by omega)
  have hDfam' : ∫⁻ omega, ((((Finset.univ :
        Finset (NFInnerHalfIndex d (K : ℤ) j N)).card : ℝ≥0∞))⁻¹ *
      ∑ q : NFInnerHalfIndex d (K : ℤ) j N, ENNReal.ofReal
        (F.toCellFamily.dirichlet q omega ^ (4 : ℕ))) ∂M.P.toMeasure ≤
      ((((3 ^ d : ℕ)) : ℝ≥0∞) * CD0) *
        (ENNReal.ofReal M.delta) ^ (68 : ℕ) := by
    refine hDfam.trans (le_of_eq ?_)
    rw [hpow, mul_assoc]
  have hfoldbound :=
    oneStepTwoRadiusNeumannHessianReadout_le_delta_sixtyEight_of_budgets
      (mu := M.P.toMeasure) (Finset.univ) (nfNestedCell N) F herr hDfam'
      hH₁fam hH₂fam
  -- transfer onto the source cells
  have hcard : (Finset.univ : Finset (NFInnerHalfIndex d (K : ℤ) j N)).card ≤
      (oneStepSourceCells d K n M.delta).card := by
    have hbase := nfNestedIndex_card_le_descendantsAtDepth_card
      (d := d) (K := (K : ℤ)) (j := j) (N := N) (a := 1) (k := N - 1)
      le_rfl (by omega)
    rw [hjN] at hbase
    exact hbase
  have htransfer := lintegral_normalized_ofReal_nfExtendByZero_pow_four_le
    (mu := M.P.toMeasure) (nfNestedCell N) F.toCellFamily.neumann
    (oneStepSourceCells d K n M.delta) hcard
  calc
    _ ≤ ∫⁻ omega, ((((Finset.univ :
          Finset (NFInnerHalfIndex d (K : ℤ) j N)).card : ℝ≥0∞))⁻¹ *
        ∑ q : NFInnerHalfIndex d (K : ℤ) j N, ENNReal.ofReal
          (F.toCellFamily.neumann q omega ^ (4 : ℕ))) ∂M.P.toMeasure :=
      htransfer
    _ = oneStepTwoRadiusNeumannHessianReadout M.P.toMeasure Finset.univ
        (nfNestedCell N) F :=
      (oneStepTwoRadiusNeumannHessianReadout_eq_toCellFamily _ _ _ _).symm
    _ ≤ (64 * ((((3 ^ d : ℕ) : ℝ≥0∞) * CD0) + C₁ + C₂)) *
        (ENNReal.ofReal M.delta) ^ (68 : ℕ) := hfoldbound
    _ = (64 * ((((3 ^ d : ℕ) : ℝ≥0∞) * CD0) + C₁ + C₂)) *
        ENNReal.ofReal (M.delta ^ (68 : ℕ)) := by
      rw [hpow]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold
