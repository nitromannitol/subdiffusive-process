module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold.InnerHalfSourceCellBudget
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold.InnerHalfCoverage
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold.DualSourceOscillatory

@[expose] public section

/-!
# The `delta ^ 30` dual oscillatory envelope over the shared-parent family

Mirror of `exists_oneStepDualOscillatory_sourceCells_budget`
(`DualSourceOscillatory.lean`) with the shared-parent family of
`InnerHalfSourceCellBudget.lean` in place of the fixed-concentric-interior
one.  Conjuncts one, two and four of `DualCellMajorantInputs` are unchanged
byte for byte; what changes is the *carrier* of the envelope: its cells are
now **all** source-scale cells inside the retained overlap centres, not only
those in the fixed concentric interior of their parent.
-/

open MeasureTheory Homogenization
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure
open SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- **The dual oscillatory envelope on the one-step source cells, over the
shared-parent family.**

Conjuncts one, two and four of `DualCellMajorantInputs`, with the envelope
carried by the shared-parent two-radius family: past
`oneStepLocalizationScale n M.delta + (nfFoldRadius (nfAxisHarmonicDepth d hd)
M.delta + 1)` the envelope is the literal `oneStepDualOscillatoryMajorant` of
the one-step Neumann corrector's cell Hessian on every depth-`(N - 1)`
descendant of every retained overlap centre. -/
theorem exists_oneStepDualOscillatory_innerHalf_sourceCells_budget
    (d : ℕ) [NeZero d] (hd : 3 ≤ d) (D : ℝ) (hD0 : 0 ≤ D) :
    ∃ delta0 O : ℝ, 0 < delta0 ∧ 0 < O ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
        ∀ (n h K : ℕ) (p : Vec d), vecNormSq p = 1 → ∀ hh : 0 < h,
          (h : ℝ) ≤ M.delta⁻¹ →
          16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n →
          oneStepLocalizationScale n M.delta ≤ K →
          ∃ oscillatory : TriadicCube d → Sample d → ℝ,
            (∀ R ∈ oneStepSourceCells d K n M.delta,
              Integrable (oscillatory R) M.P.toMeasure) ∧
            (∀ R ∈ oneStepSourceCells d K n M.delta,
              ∀ omega, 0 ≤ oscillatory R omega) ∧
            ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
                ∑ R ∈ oneStepSourceCells d K n M.delta,
                  ∫ omega, oscillatory R omega ∂M.P.toMeasure ≤
              O * M.delta ^ (30 : ℕ) * (ahom M n)⁻¹) ∧
            (oneStepLocalizationScale n M.delta +
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
                (∀ S ∈ overlapCentersAtDepth (originCube d (K : ℤ)) j,
                  ∀ R ∈ descendantsAtDepth S (N - 1),
                    ∃ q : NFInnerHalfIndex d (K : ℤ) j N,
                      nfNestedCell N q = R) ∧
                oscillatory = oneStepDualOscillatoryMajorant M n h D
                  (nfExtendByZero (nfNestedCell N)
                    F.toCellFamily.neumann)) := by
  obtain ⟨CB, hCBtop, hcellB⟩ :=
    exists_nfInnerHalfNeumannSourceCellB_lintegral_budget d hd
  obtain ⟨delta0, O, hdelta0, hO, henvelope⟩ :=
    exists_oneStepDualOscillatoryFiniteBudget_of_cellB d D CB.toReal hD0
      ENNReal.toReal_nonneg
  refine ⟨delta0, O, hdelta0, hO, ?_⟩
  intro M hM n h K p hp hh hblock hsource hK
  by_cases hbig : oneStepLocalizationScale n M.delta +
      (nfFoldRadius (nfAxisHarmonicDepth d hd) M.delta + 1) ≤ K
  · obtain ⟨j, N, F, hNdef, hjN, hgrad, hcellmem, hbudget⟩ :=
      hcellB M n h K p hp hh hblock hsource hbig
    set B : TriadicCube d → Sample d → ℝ :=
      nfExtendByZero (nfNestedCell N) F.toCellFamily.neumann with hB
    have hBmeas : ∀ R ∈ oneStepSourceCells d K n M.delta, Measurable (B R) :=
      fun R _ ↦ measurable_nfExtendByZero
        (fun i ↦ F.toCellFamily.measurable_neumann i (Finset.mem_univ i)) R
    have hB0 : ∀ R ∈ oneStepSourceCells d K n M.delta,
        ∀ omega, 0 ≤ B R omega :=
      fun R _ ↦ nfExtendByZero_nonneg
        (fun i omega ↦ F.toCellFamily.neumann_nonneg i (Finset.mem_univ i)
          omega) R
    have hKBtop : CB * ENNReal.ofReal (M.delta ^ (68 : ℕ)) ≠ ∞ :=
      ENNReal.mul_ne_top hCBtop ENNReal.ofReal_ne_top
    obtain ⟨hBint, hBbudget0⟩ :=
      finiteFamily_four_budget_of_lintegral_average
        (oneStepSourceCells d K n M.delta)
        (oneStepSourceCells_nonempty d K n M.delta) B hBmeas hB0 hKBtop
        hbudget
    have hKBreal : (CB * ENNReal.ofReal (M.delta ^ (68 : ℕ))).toReal =
        CB.toReal * M.delta ^ (68 : ℕ) := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
        (by positivity : (0 : ℝ) ≤ M.delta ^ (68 : ℕ))]
    obtain ⟨hEint, hEbudget⟩ := henvelope M hM n h K hblock hsource hK B
      hBmeas hB0 hBint (by simpa only [hKBreal] using hBbudget0)
    refine ⟨oneStepDualOscillatoryMajorant M n h D B, hEint, ?_, hEbudget,
      fun _ ↦ ⟨j, N, F, hNdef, hjN, hgrad, hcellmem,
        fun _S hS _R hR ↦ exists_nfInnerHalfIndex_cell_eq hS hR, rfl⟩⟩
    intro R hR omega
    exact mul_nonneg
      (mul_nonneg (oneStepDualCellEnergyConst_nonneg d)
        (dualPoincareFactor_cell_nonneg M n h R omega))
      (oneStepCellBesovError_nonneg
        (mul_nonneg hD0 (hB0 R hR omega)) (hB0 R hR omega))
  · refine ⟨fun _ _ ↦ (0 : ℝ), fun _ _ ↦ integrable_const _,
      fun _ _ _ ↦ le_refl 0, ?_, fun hcontra ↦ absurd hcontra hbig⟩
    have hzero : (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ _R ∈ oneStepSourceCells d K n M.delta,
          ∫ _omega : Sample d, (0 : ℝ) ∂M.P.toMeasure = 0 := by
      simp
    rw [hzero]
    have hd0 : 0 < M.delta := M.shellPrefix.delta_pos
    have hahom : 0 < (ahom M n)⁻¹ := inv_pos.mpr (ahom_pos M n)
    positivity

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold
