module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.CutoffGammaOneTail
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.UncutGammaOneTail

@[expose] public section

/-!
# Composing the proved Γ₁ tails with the deterministic rows

Both Γ₁ tails are now theorems (`exists_cutoffGammaOneTail`,
`exists_uncutGammaOneTail`), each producing *one* constant.  The deterministic
row packages will produce their own.  Reconciling the two is exactly the
monotonicity of the frozen Γ₁ statement in `C`, proved here: enlarging `C`
strengthens both hypotheses (`δ ≤ C⁻¹` and the α-window) and weakens the
conclusion (bigger prefactor, smaller shift, smaller rate).

The upshot, `exists_cutoffHolderRegularityInterior_of_rows`, is the frozen
interior anchor from the deterministic rows alone: **no probabilistic
obligation survives.**
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ### Monotonicity of the frozen Γ₁ right-hand side -/

/-- The frozen Γ₁ bound is monotone in its constant. -/
theorem gammaOneRHS_mono (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {C C' alpha : ℝ}
    {k : ℕ} (hC : 0 < C) (hCC' : C ≤ C') :
    gammaOneRHS M C alpha k ≤ gammaOneRHS M C' alpha k := by
  have hC' : 0 < C' := lt_of_lt_of_le hC hCC'
  have hDnn : (0 : ℝ) ≤ M.delta ^ 2 * |Real.log M.delta| := by positivity
  rcases eq_or_lt_of_le hDnn with hD0 | hD
  · rw [gammaOneRHS_eq, gammaOneRHS_eq, ← hD0]
    simp only [mul_zero, div_zero, neg_zero, Real.exp_zero, mul_one]
    exact hCC'
  · have hmax : max ((k : ℝ) - C') 0 ≤ max ((k : ℝ) - C) 0 :=
      max_le_max (by linarith) le_rfl
    have hexp : (1 - alpha) ^ 2 * max ((k : ℝ) - C') 0 /
        (C' * (M.delta ^ 2 * |Real.log M.delta|)) ≤
          (1 - alpha) ^ 2 * max ((k : ℝ) - C) 0 /
            (C * (M.delta ^ 2 * |Real.log M.delta|)) :=
      gammaOne_exponent_le hC' hC hD hCC' hmax
    rw [gammaOneRHS_eq, gammaOneRHS_eq]
    exact exp_bound_le hC.le hCC' hexp

/-- Enlarging the constant preserves the finite-cutoff Γ₁ tail. -/
theorem cutoffGammaOneTailAt_mono {C C' C1 C2 : ℝ} {step : ℕ}
    (hC : 0 < C) (hCC' : C ≤ C')
    (h : CutoffGammaOneTailAt d C C1 C2 step) :
    CutoffGammaOneTailAt d C' C1 C2 step := by
  intro M hdelta alpha halpha L m k hk
  have hdelta0 : 0 < M.delta := M.shellPrefix.delta_pos
  have hdeltaC : M.delta ≤ C⁻¹ := hdelta.trans (inv_anti₀ hC hCC')
  have hroot : 0 ≤ |Real.log M.delta| ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (abs_nonneg _) _
  have halphaC : alpha ∈ Set.Icc (1 / 2 : ℝ)
      (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)) := by
    refine ⟨halpha.1, halpha.2.trans ?_⟩
    have hstep : C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ) ≤
        C' * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCC' hdelta0.le) hroot
    linarith
  exact (h M hdeltaC alpha halphaC L m k hk).trans
    (ENNReal.ofReal_le_ofReal (gammaOneRHS_mono M hC hCC'))

/-- Enlarging the constant preserves the cutoff-independent Γ₁ tail. -/
theorem uncutGammaOneTailAt_mono {C C' C1 C2 : ℝ} {step : ℕ}
    (hC : 0 < C) (hCC' : C ≤ C')
    (h : UncutGammaOneTailAt d C C1 C2 step) :
    UncutGammaOneTailAt d C' C1 C2 step := by
  intro M hdelta alpha halpha m k hk
  have hdelta0 : 0 < M.delta := M.shellPrefix.delta_pos
  have hdeltaC : M.delta ≤ C⁻¹ := hdelta.trans (inv_anti₀ hC hCC')
  have hroot : 0 ≤ |Real.log M.delta| ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (abs_nonneg _) _
  have halphaC : alpha ∈ Set.Icc (1 / 2 : ℝ)
      (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)) := by
    refine ⟨halpha.1, halpha.2.trans ?_⟩
    have hstep : C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ) ≤
        C' * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCC' hdelta0.le) hroot
    linarith
  exact (h M hdeltaC alpha halphaC m k hk).trans
    (ENNReal.ofReal_le_ofReal (gammaOneRHS_mono M hC hCC'))

/-! ### The deterministic rows at the named carriers -/

/-- The three frozen interior rows at the finite-cutoff stopping carrier. -/
def InteriorCutoffRowsAt (d : ℕ) (C C1 C2 : ℝ) (step : ℕ) : Prop :=
  ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ C⁻¹ →
    ∀ alpha ∈ Set.Icc (1 / 2 : ℝ)
        (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
      ∀ L m : ℕ, ∀ ω,
        ∀ (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
          IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω)
              (cube d m) u g →
          MemHolder (cube d m) (1 / 2) g →
          InteriorHolderRegularityConclusions M C L ω alpha m
            (Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
              (Section6Stopping.holderStoppingLambda C1 alpha)
              (Section6Stopping.holderStoppingEpsilon C2 alpha) step m ω) u g

/-- The three frozen interior rows at the cutoff-independent carrier, uniformly
in every cutoff `J ≥ m`. -/
def InteriorUncutRowsAt (d : ℕ) (C C1 C2 : ℝ) (step : ℕ) : Prop :=
  ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ C⁻¹ →
    ∀ alpha ∈ Set.Icc (1 / 2 : ℝ)
        (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
      ∀ m : ℕ, ∀ J : ℕ, m ≤ J → ∀ ω,
        ∀ (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
          IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M J ω)
              (cube d m) u g →
          MemHolder (cube d m) (1 / 2) g →
          InteriorHolderRegularityConclusions M C J ω alpha m
            (Section6Stopping.measurableHolderStoppingScale M alpha
              (Section6Stopping.holderStoppingLambda C1 alpha)
              (Section6Stopping.holderStoppingEpsilon C2 alpha) step m ω) u g

/-- Tail plus rows give the fixed-cutoff sample-space package. -/
theorem interiorCutoffPathwiseInput_of_tailAndRows {C C1 C2 : ℝ} {step : ℕ}
    (htail : CutoffGammaOneTailAt d C C1 C2 step)
    (hrows : InteriorCutoffRowsAt d C C1 C2 step) :
    InteriorCutoffPathwiseInput d C := by
  intro M hdelta alpha halpha L m
  refine ⟨Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
      (Section6Stopping.holderStoppingLambda C1 alpha)
      (Section6Stopping.holderStoppingEpsilon C2 alpha) step m,
    Section6Stopping.measurable_measurableCutoffHolderStoppingScale _ _ _ _ _ _ _,
    fun ω => Section6Stopping.measurableCutoffHolderStoppingScale_pos _ _ _ _ _ _ _ ω,
    fun k hk => htail M hdelta alpha halpha L m k hk,
    fun ω u g hsol hg => hrows M hdelta alpha halpha L m ω u g hsol hg⟩

/-- Tail plus rows give the cutoff-uniform sample-space package. -/
theorem interiorCutoffUniformInput_of_tailAndRows {C C1 C2 : ℝ} {step : ℕ}
    (htail : UncutGammaOneTailAt d C C1 C2 step)
    (hrows : InteriorUncutRowsAt d C C1 C2 step) :
    InteriorCutoffUniformInput d C := by
  intro M hdelta alpha halpha m
  refine ⟨Section6Stopping.measurableHolderStoppingScale M alpha
      (Section6Stopping.holderStoppingLambda C1 alpha)
      (Section6Stopping.holderStoppingEpsilon C2 alpha) step m,
    Section6Stopping.measurable_measurableHolderStoppingScale _ _ _ _ _ _,
    fun ω => Section6Stopping.measurableHolderStoppingScale_pos _ _ _ _ _ _ ω,
    fun k hk => htail M hdelta alpha halpha m k hk,
    fun J hJ ω u g hsol hg => hrows M hdelta alpha halpha m J hJ ω u g hsol hg⟩

/-- **The frozen interior anchor from the deterministic rows alone.**  Every
probabilistic obligation is discharged: the two Γ₁ tails are theorems, and the
constant is reconciled by monotonicity. -/
theorem exists_cutoffHolderRegularityInterior_of_rows (d : ℕ) [NeZero d]
    (step : ℕ) {C0 C1 C2 : ℝ} (hC1 : 1 ≤ C1) (hC2 : 1 ≤ C2)
    (hrows : ∀ C : ℝ, C0 ≤ C → InteriorCutoffRowsAt d C C1 C2 step)
    (hrowsU : ∀ C : ℝ, C0 ≤ C → InteriorUncutRowsAt d C C1 C2 step) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      (M.delta ≤ C⁻¹ →
      ∀ alpha ∈ Set.Icc (1 / 2 : ℝ)
          (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
        ∀ L m : ℕ,
          (∃ X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
            Measurable X ∧ (∀ ω, 0 < X ω) ∧
            (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < X ω} ≤ ENNReal.ofReal
              (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ ω, ∀ (u : H1Function (openCubeSet (originCube d m)))
                (g : Vec d → Vec d),
              IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω)
                  (cube d m) u g →
              MemHolder (cube d m) (1 / 2) g →
              InteriorHolderRegularityConclusions M C L ω alpha m (X ω) u g) ∧
          (m ≤ L → ∃ Xuncut : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
            Measurable Xuncut ∧ (∀ ω, 0 < Xuncut ω) ∧
            (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < Xuncut ω} ≤ ENNReal.ofReal
              (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ J : ℕ, m ≤ J → ∀ ω,
              ∀ (u : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M J ω)
                    (cube d m) u g →
                MemHolder (cube d m) (1 / 2) g →
                InteriorHolderRegularityConclusions M C J ω alpha m (Xuncut ω) u g) ∧
          ∀ y : Vec d,
            (∃ Xy : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
              Measurable Xy ∧ (∀ ω, 0 < Xy ω) ∧
              (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < Xy ω} ≤ ENNReal.ofReal
                (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
              ∀ ω, ∀ (u : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                IsDivFormWeakSolutionOn
                    (_root_.SubdiffusiveProcess.Model.aCutoff M L
                      (translatePotentialSample y ω))
                    (cube d m) u g →
                MemHolder (cube d m) (1 / 2) g →
                InteriorHolderRegularityConclusions M C L (translatePotentialSample y ω)
                  alpha m (Xy ω) u g) ∧
            (m ≤ L → ∃ XuncutY : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
              Measurable XuncutY ∧ (∀ ω, 0 < XuncutY ω) ∧
              (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < XuncutY ω} ≤ ENNReal.ofReal
                (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
              ∀ J : ℕ, m ≤ J → ∀ ω,
                ∀ (u : H1Function (openCubeSet (originCube d m)))
                    (g : Vec d → Vec d),
                  IsDivFormWeakSolutionOn
                      (_root_.SubdiffusiveProcess.Model.aCutoff M J
                        (translatePotentialSample y ω))
                      (cube d m) u g →
                  MemHolder (cube d m) (1 / 2) g →
                  InteriorHolderRegularityConclusions M C J (translatePotentialSample y ω)
                    alpha m (XuncutY ω) u g)) := by
  obtain ⟨Ca, hCa, htailCut⟩ := exists_cutoffGammaOneTail d step hC1 hC2
  obtain ⟨Cb, hCb, htailUncut⟩ := exists_uncutGammaOneTail d step hC1 hC2
  have hCposMax : 0 < max (max Ca Cb) C0 :=
    lt_of_lt_of_le hCa (le_trans (le_max_left _ _) (le_max_left _ _))
  have hcut := cutoffGammaOneTailAt_mono (C' := max (max Ca Cb) C0) hCa
    (le_trans (le_max_left Ca Cb) (le_max_left _ _)) htailCut
  have huncut := uncutGammaOneTailAt_mono (C' := max (max Ca Cb) C0) hCb
    (le_trans (le_max_right Ca Cb) (le_max_left _ _)) htailUncut
  exact exists_cutoffHolderRegularityInterior_of_inputs d _ hCposMax
    (interiorCutoffPathwiseInput_of_tailAndRows hcut (hrows _ (le_max_right _ _)))
    (interiorCutoffUniformInput_of_tailAndRows huncut (hrowsU _ (le_max_right _ _)))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
