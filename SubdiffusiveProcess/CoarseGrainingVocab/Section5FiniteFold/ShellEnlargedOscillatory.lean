import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepShellForcingCellBudget
import SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold.InnerHalfDualSourceOscillatory




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

/-! ## Two elementary facts -/

/-- A crude but sufficient fourth-power expansion. -/
theorem add_pow_four_le_sixteen {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ (4 : ℕ) ≤ 16 * (a ^ (4 : ℕ) + b ^ (4 : ℕ)) := by
  have ha4 : 0 ≤ a ^ (4 : ℕ) := by positivity
  have hb4 : 0 ≤ b ^ (4 : ℕ) := by positivity
  rcases le_total a b with hab | hab
  · have hle : a + b ≤ 2 * b := by linarith
    have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ a + b) hle 4
    nlinarith
  · have hle : a + b ≤ 2 * a := by linarith
    have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ a + b) hle 4
    nlinarith

/-- The shell-Jacobian cell size is nonnegative. -/
theorem oneStepShellForcingCellB_nonneg {d : ℕ} {Q R : TriadicCube d}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (omega : Sample d) (q : Vec d) (hh : 0 < h) :
    0 ≤ oneStepShellForcingCellB (Q := Q) (R := R) M n h omega q hh := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.oneStepShellForcingCellB_nonneg_support (d := d) (Q := Q) (R := R) (M := M) (n := n) (h := h) (omega := omega) (q := q) (hh := hh)

/-! ## The enlarged cell size and the shell budget -/

/-- The cell size that the paper-sign quarter-Besov carrier actually delivers:
the family's Neumann cell Hessian **plus** the shell-Jacobian term, scaled by
the dimension. -/
def nfShellEnlargedCellB {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n h K : ℕ) (q : Vec d) (hh : 0 < h)
    (B : TriadicCube d → Sample d → ℝ)
    (R : TriadicCube d) (omega : Sample d) : ℝ :=
  (d : ℝ) * (oneStepShellForcingCellB (Q := originCube d (K : ℤ)) (R := R)
    M n h omega q hh + B R omega)



def ShellForcingCellBFourthBudget (d : ℕ) [NeZero d] : Prop :=
  ∃ CS : ℝ, 0 ≤ CS ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h K : ℕ) (q : Vec d),
      vecNormSq q = 1 → ∀ hh : 0 < h, (h : ℝ) ≤ M.delta⁻¹ →
        16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n →
        oneStepLocalizationScale n M.delta ≤ K →
        (∀ R ∈ oneStepSourceCells d K n M.delta,
          Integrable (fun omega ↦
            oneStepShellForcingCellB (Q := originCube d (K : ℤ)) (R := R)
              M n h omega q hh ^ (4 : ℕ)) M.P.toMeasure) ∧
        ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
            ∑ R ∈ oneStepSourceCells d K n M.delta,
              ∫ omega, oneStepShellForcingCellB
                (Q := originCube d (K : ℤ)) (R := R)
                M n h omega q hh ^ (4 : ℕ) ∂M.P.toMeasure ≤
          CS * M.delta ^ (68 : ℕ))

/-! ## The enlarged fold -/

/-- **The dual oscillatory envelope with the shell-enlarged cell size.**
Conjuncts one, two and four of `DualCellMajorantInputs`, unchanged in shape,
for the envelope built on `nfShellEnlargedCellB` — the cell size that the
paper-sign quarter-Besov carrier delivers. -/
theorem exists_oneStepDualOscillatory_innerHalf_sourceCells_budget_shellEnlarged
    (d : ℕ) [NeZero d] (hd : 3 ≤ d) (D : ℝ) (hD0 : 0 ≤ D)
    (hshell : ShellForcingCellBFourthBudget d) :
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
                  (nfShellEnlargedCellB M n h K p hh
                    (nfExtendByZero (nfNestedCell N)
                      F.toCellFamily.neumann))) := by
  classical
  obtain ⟨CS, hCS0, hshellBudget⟩ := hshell
  obtain ⟨CB, hCBtop, hcellB⟩ :=
    exists_nfInnerHalfNeumannSourceCellB_lintegral_budget d hd
  obtain ⟨delta0, O, hdelta0, hO, henvelope⟩ :=
    exists_oneStepDualOscillatoryFiniteBudget_of_cellB d D
      (16 * (d : ℝ) ^ (4 : ℕ) * (CS + CB.toReal)) hD0
      (by positivity)
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
    have hBbudget : (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega, B R omega ^ (4 : ℕ) ∂M.P.toMeasure ≤
        CB.toReal * M.delta ^ (68 : ℕ) := by
      simpa only [hKBreal] using hBbudget0
    obtain ⟨hSint, hSbudget⟩ :=
      hshellBudget M n h K p hp hh hblock hsource hK
    -- the enlarged cell size
    set B' : TriadicCube d → Sample d → ℝ :=
      nfShellEnlargedCellB M n h K p hh B with hB'
    have hB'eq : ∀ R omega, B' R omega =
        (d : ℝ) * (oneStepShellForcingCellB
          (Q := originCube d (K : ℤ)) (R := R) M n h omega p hh +
          B R omega) := fun R omega ↦ rfl
    have hSmeas : ∀ R : TriadicCube d, Measurable fun omega ↦
        oneStepShellForcingCellB (Q := originCube d (K : ℤ)) (R := R)
          M n h omega p hh := fun R ↦
      measurable_oneStepShellForcingCellB
        (Q := originCube d (K : ℤ)) (R := R) M n h p hh
    have hB'meas : ∀ R ∈ oneStepSourceCells d K n M.delta,
        Measurable (B' R) := by
      intro R hR
      simpa only [hB', nfShellEnlargedCellB] using
        (measurable_const.mul ((hSmeas R).add (hBmeas R hR)))
    have hB'0 : ∀ R ∈ oneStepSourceCells d K n M.delta,
        ∀ omega, 0 ≤ B' R omega := by
      intro R hR omega
      rw [hB'eq]
      exact mul_nonneg (Nat.cast_nonneg d)
        (add_nonneg (oneStepShellForcingCellB_nonneg M n h omega p hh)
          (hB0 R hR omega))
    have hdom : ∀ R ∈ oneStepSourceCells d K n M.delta, ∀ omega,
        B' R omega ^ (4 : ℕ) ≤ 16 * (d : ℝ) ^ (4 : ℕ) *
          ((oneStepShellForcingCellB (Q := originCube d (K : ℤ)) (R := R)
              M n h omega p hh) ^ (4 : ℕ) + B R omega ^ (4 : ℕ)) := by
      intro R hR omega
      rw [hB'eq, mul_pow]
      have := add_pow_four_le_sixteen
        (oneStepShellForcingCellB_nonneg (Q := originCube d (K : ℤ))
          (R := R) M n h omega p hh) (hB0 R hR omega)
      nlinarith [pow_nonneg (Nat.cast_nonneg d : (0:ℝ) ≤ (d : ℝ)) 4]
    have hboundInt : ∀ R ∈ oneStepSourceCells d K n M.delta,
        Integrable (fun omega ↦ 16 * (d : ℝ) ^ (4 : ℕ) *
          ((oneStepShellForcingCellB (Q := originCube d (K : ℤ)) (R := R)
              M n h omega p hh) ^ (4 : ℕ) + B R omega ^ (4 : ℕ)))
          M.P.toMeasure := by
      intro R hR
      exact ((hSint R hR).add (hBint R hR)).const_mul _
    have hB'int : ∀ R ∈ oneStepSourceCells d K n M.delta,
        Integrable (fun omega ↦ B' R omega ^ (4 : ℕ)) M.P.toMeasure := by
      intro R hR
      refine Integrable.mono' (hboundInt R hR)
        (((hB'meas R hR).pow_const 4).aestronglyMeasurable) ?_
      filter_upwards with omega
      rw [Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ B' R omega ^ (4 : ℕ))]
      exact hdom R hR omega
    have hB'budget : (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega, B' R omega ^ (4 : ℕ) ∂M.P.toMeasure ≤
        (16 * (d : ℝ) ^ (4 : ℕ) * (CS + CB.toReal)) * M.delta ^ (68 : ℕ) := by
      have hcell : ∀ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega, B' R omega ^ (4 : ℕ) ∂M.P.toMeasure ≤
            16 * (d : ℝ) ^ (4 : ℕ) *
              ((∫ omega, (oneStepShellForcingCellB
                  (Q := originCube d (K : ℤ)) (R := R)
                  M n h omega p hh) ^ (4 : ℕ) ∂M.P.toMeasure) +
                ∫ omega, B R omega ^ (4 : ℕ) ∂M.P.toMeasure) := by
        intro R hR
        have hmono := integral_mono (hB'int R hR) (hboundInt R hR)
          (fun omega ↦ hdom R hR omega)
        rw [integral_const_mul,
          integral_add (hSint R hR) (hBint R hR)] at hmono
        exact hmono
      have hsum := Finset.sum_le_sum hcell
      have hcard0 : (0 : ℝ) ≤ ((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹ := by
        positivity
      have hstep := mul_le_mul_of_nonneg_left hsum hcard0
      have hsplit : (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            16 * (d : ℝ) ^ (4 : ℕ) *
              ((∫ omega, (oneStepShellForcingCellB
                  (Q := originCube d (K : ℤ)) (R := R)
                  M n h omega p hh) ^ (4 : ℕ) ∂M.P.toMeasure) +
                ∫ omega, B R omega ^ (4 : ℕ) ∂M.P.toMeasure) =
          16 * (d : ℝ) ^ (4 : ℕ) *
            (((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
                ∑ R ∈ oneStepSourceCells d K n M.delta,
                  ∫ omega, (oneStepShellForcingCellB
                    (Q := originCube d (K : ℤ)) (R := R)
                    M n h omega p hh) ^ (4 : ℕ) ∂M.P.toMeasure) +
              ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
                ∑ R ∈ oneStepSourceCells d K n M.delta,
                  ∫ omega, B R omega ^ (4 : ℕ) ∂M.P.toMeasure)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        ring
      rw [hsplit] at hstep
      refine hstep.trans ?_
      have hconst0 : (0 : ℝ) ≤ 16 * (d : ℝ) ^ (4 : ℕ) := by positivity
      have := add_le_add hSbudget hBbudget
      calc
        16 * (d : ℝ) ^ (4 : ℕ) * (_ + _) ≤
            16 * (d : ℝ) ^ (4 : ℕ) *
              (CS * M.delta ^ (68 : ℕ) + CB.toReal * M.delta ^ (68 : ℕ)) :=
          mul_le_mul_of_nonneg_left this hconst0
        _ = _ := by ring
    obtain ⟨hEint, hEbudget⟩ := henvelope M hM n h K hblock hsource hK B'
      hB'meas hB'0 hB'int hB'budget
    refine ⟨oneStepDualOscillatoryMajorant M n h D B', hEint, ?_, hEbudget,
      fun _ ↦ ⟨j, N, F, hNdef, hjN, hgrad, hcellmem,
        fun _S hS _R hR ↦ exists_nfInnerHalfIndex_cell_eq hS hR, rfl⟩⟩
    intro R hR omega
    exact mul_nonneg
      (mul_nonneg (oneStepDualCellEnergyConst_nonneg d)
        (dualPoincareFactor_cell_nonneg M n h R omega))
      (oneStepCellBesovError_nonneg
        (mul_nonneg hD0 (hB'0 R hR omega)) (hB'0 R hR omega))
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
