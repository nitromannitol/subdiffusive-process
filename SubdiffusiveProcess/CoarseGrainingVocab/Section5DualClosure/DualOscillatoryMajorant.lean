module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepFinalSpecialization
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSourceCellEllipticityCovariance
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSourceEllipticityFactors
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNeumannHessianPackage
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCellMomentAggregation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepRandomCellSpecialization

@[expose] public section




open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d



def oneStepDualQuarterCellConst (d : ℕ) : ℝ :=
  max (oneStepQuarterCellConst d) (max 2 (cubeBesovW12EmbeddingConstant d))

theorem oneStepQuarterCellConst_le_oneStepDualQuarterCellConst (d : ℕ) :
    oneStepQuarterCellConst d ≤ oneStepDualQuarterCellConst d :=
  le_max_left _ _

theorem cubeBesovW12EmbeddingConstant_max_le_oneStepDualQuarterCellConst
    (d : ℕ) :
    max 2 (cubeBesovW12EmbeddingConstant d) ≤ oneStepDualQuarterCellConst d :=
  le_max_right _ _

theorem oneStepDualQuarterCellConst_pos (d : ℕ) :
    0 < oneStepDualQuarterCellConst d :=
  lt_of_lt_of_le (oneStepQuarterCellConst_pos d) (le_max_left _ _)

/-- Dimension-only coefficient in the dual quarter-Besov cell estimate.
Same shape as `oneStepPrimalCellEnergyConst`, on the shared constant. -/
def oneStepDualCellEnergyConst (d : ℕ) : ℝ :=
  2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
    oneStepDualQuarterCellConst d) ^ 2

theorem oneStepDualCellEnergyConst_nonneg (d : ℕ) :
    0 ≤ oneStepDualCellEnergyConst d := by
  dsimp only [oneStepDualCellEnergyConst]
  positivity

/-- Measurable lower envelope for the selected oscillatory dual cell energy.
Mirror of `oneStepPrimalOscillatoryMajorant` with the lower coarse-Poincaré
factor; `B` is supplied by the caller as the samplewise cell Hessian size, so
this definition is independent of which Calderón--Zygmund package produces
it. -/
def oneStepDualOscillatoryMajorant {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (D : ℝ)
    (B : Homogenization.TriadicCube d → Sample d → ℝ)
    (R : Homogenization.TriadicCube d) (omega : Sample d) : ℝ :=
  oneStepDualCellEnergyConst d *
    oneStepLowerPoincareEnergyFactorMeasurable M (n + h)
      (oneStepLocalizationScale n M.delta)
      (translatePotentialSequence (triadicCubeShift R) omega) *
    oneStepCellBesovError (D * B R omega) (B R omega)

/-- The dual oscillatory envelope is exactly the scaled Besov fold that
`finiteFamily_scaledCellBesovMajorant_budget` consumes. -/
theorem oneStepDualOscillatoryMajorant_eq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (D : ℝ)
    (B : Homogenization.TriadicCube d → Sample d → ℝ)
    (R : Homogenization.TriadicCube d) :
    oneStepDualOscillatoryMajorant M n h D B R =
      fun omega ↦ oneStepDualCellEnergyConst d *
        oneStepLowerPoincareEnergyFactorMeasurable M (n + h)
          (oneStepLocalizationScale n M.delta)
          (translatePotentialSequence (triadicCubeShift R) omega) *
        oneStepCellBesovError (D * B R omega) (B R omega) := rfl

/-! ## The dual coarse-Poincaré factor finite budget -/



theorem exists_oneStepDualPoincareFactorFiniteBudget
    {d : ℕ} [NeZero d] :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
        ∀ (n h K : ℕ), (h : ℝ) ≤ M.delta⁻¹ →
          16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n →
          oneStepLocalizationScale n M.delta ≤ K →
          let F := fun R omega ↦
            oneStepLowerPoincareEnergyFactorMeasurable M (n + h)
              (oneStepLocalizationScale n M.delta)
              (translatePotentialSequence (triadicCubeShift R) omega)
          (∀ R ∈ oneStepSourceCells d K n M.delta,
            Integrable (fun omega ↦ F R omega ^ (2 : ℕ)) M.P.toMeasure) ∧
          (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
              ∑ R ∈ oneStepSourceCells d K n M.delta,
                ∫ omega, F R omega ^ (2 : ℕ) ∂M.P.toMeasure ≤
            (C * (ahom M n)⁻¹) ^ (2 : ℕ) := by
  obtain ⟨delta0, C0, hdelta0, hC0, hsource⟩ :=
    exists_sourceScale_highCutoff_ellipticity_moments (d := d)
  let D : ℝ := Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) ^ 2
  let C : ℝ := D * C0
  have hD : 0 < D := by
    dsimp only [D, Ch03.poincareDiscountFactor]
    exact sq_pos_of_pos <| Real.rpow_pos_of_pos
      (Ch02.book_geometricDiscount_pos (by norm_num)) _
  have hC : 0 < C := mul_pos hD hC0
  refine ⟨delta0, C, hdelta0, hC, ?_⟩
  intro M hM n h K hblock hstart hK
  let j := oneStepLocalizationScale n M.delta
  let X : Sample d → ℝ := fun omega ↦
    (cutoffLowerEllipticityMeasurable M (n + h) j omega)⁻¹
  let F0 := oneStepLowerPoincareEnergyFactorMeasurable M (n + h) j
  obtain ⟨_hupperInt, _hupperBudget, hXint, hXbudget⟩ :=
    hsource M hM n h hblock (oneStepLocalizationDepth_le hstart)
  have hFX : F0 =ᵐ[M.P.toMeasure] fun omega ↦ D * X omega := by
    filter_upwards [cutoffLowerEllipticityMeasurable_ae_eq M (n + h) j]
      with omega hXeq
    simp only [F0, oneStepLowerPoincareEnergyFactorMeasurable,
      oneStepLowerInvEllipticityRatioMeasurable, X]
    rw [max_eq_left]
    · dsimp only [D]
      rw [mul_assoc, ← mul_assoc ((ahom M (n + h))⁻¹),
        inv_mul_cancel₀ (ahom_pos M (n + h)).ne', one_mul]
    · rw [hXeq]
      exact mul_nonneg (ahom_pos M (n + h)).le
        (inv_nonneg.mpr
          (Ch04.lambdaSqCoeffField_finite_nonneg _ _ (by norm_num)
            (by norm_num)))
  have hFint : Integrable (fun omega ↦ F0 omega ^ (2 : ℕ))
      M.P.toMeasure := by
    apply (hXint.const_mul (D ^ (2 : ℕ))).congr
    filter_upwards [hFX] with omega heq
    rw [heq]
    ring
  have hFbudget : ∫ omega, F0 omega ^ (2 : ℕ) ∂M.P.toMeasure ≤
      (C * (ahom M n)⁻¹) ^ (2 : ℕ) := by
    have hsq : (fun omega ↦ F0 omega ^ (2 : ℕ)) =ᵐ[M.P.toMeasure]
        fun omega ↦ D ^ (2 : ℕ) * X omega ^ (2 : ℕ) := by
      filter_upwards [hFX] with omega heq
      rw [heq]
      ring
    calc
      _ = D ^ (2 : ℕ) * ∫ omega, X omega ^ (2 : ℕ) ∂M.P.toMeasure := by
        rw [integral_congr_ae hsq]
        rw [integral_const_mul]
      _ ≤ D ^ (2 : ℕ) * (C0 * (ahom M n)⁻¹) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hXbudget (sq_nonneg D)
      _ = (C * (ahom M n)⁻¹) ^ (2 : ℕ) := by
        dsimp only [C]
        ring
  let F := fun R omega ↦ F0
    (translatePotentialSequence (triadicCubeShift R) omega)
  have hFcell : ∀ R ∈ oneStepSourceCells d K n M.delta,
      Integrable (fun omega ↦ F R omega ^ (2 : ℕ)) M.P.toMeasure := by
    intro R _hR
    exact (measurePreserving_translatePotentialSequence M (triadicCubeShift R))
      |>.integrable_comp_of_integrable hFint
  refine ⟨hFcell, ?_⟩
  rw [normalized_finset_integral_comp_translatePotentialSequence_eq M
    (fun R ↦ triadicCubeShift R) (oneStepSourceCells d K n M.delta)
    (oneStepSourceCells_nonempty d K n M.delta)
    (fun omega ↦ F0 omega ^ (2 : ℕ)) hFint]
  exact hFbudget

/-- Measurability of the translated lower coarse-Poincaré factor, as the
finite-family fold requires. -/
theorem measurable_dualPoincareFactor_cell {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (R : Homogenization.TriadicCube d) :
    Measurable fun omega ↦
      oneStepLowerPoincareEnergyFactorMeasurable M (n + h)
        (oneStepLocalizationScale n M.delta)
        (translatePotentialSequence (triadicCubeShift R) omega) :=
  (measurable_oneStepLowerPoincareEnergyFactorMeasurable M (n + h)
    (oneStepLocalizationScale n M.delta)).comp
      (measurable_translatePotentialSequence (triadicCubeShift R))

/-- Nonnegativity of the translated lower coarse-Poincaré factor. -/
theorem dualPoincareFactor_cell_nonneg {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (R : Homogenization.TriadicCube d) (omega : Sample d) :
    0 ≤ oneStepLowerPoincareEnergyFactorMeasurable M (n + h)
      (oneStepLocalizationScale n M.delta)
      (translatePotentialSequence (triadicCubeShift R) omega) := by
  dsimp only [oneStepLowerPoincareEnergyFactorMeasurable]
  exact mul_nonneg
    (mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (ahom_pos M (n + h)).le))
    (le_max_right _ _)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure
