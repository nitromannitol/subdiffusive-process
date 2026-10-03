module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily.NestedFamilyIndex

@[expose] public section

/-!
# The nested family and its two harmonic budgets

The nested index of `NestedFamilyIndex.lean` is a *product*: an overlap centre
and an origin-parent descendant.  Both harmonic parent readouts depend on the
first factor only, so their averages collapse to the overlap-index averages
already bounded in `OverlapFamilyBudgets.lean`.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily

open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-- A product-index average of a first-factor observable collapses. -/
theorem nfProd_average_eq {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    [Nonempty ι₂] (f : ι₁ → ℝ≥0∞) :
    (((Finset.univ : Finset (ι₁ × ι₂)).card : ℝ≥0∞))⁻¹ *
        ∑ q : ι₁ × ι₂, f q.1 =
      (((Finset.univ : Finset ι₁).card : ℝ≥0∞))⁻¹ * ∑ i : ι₁, f i := by
  classical
  set c₁ : ℝ≥0∞ := ((Finset.univ : Finset ι₁).card : ℝ≥0∞) with hc₁def
  set c₂ : ℝ≥0∞ := ((Finset.univ : Finset ι₂).card : ℝ≥0∞) with hc₂def
  set X : ℝ≥0∞ := ∑ i : ι₁, f i with hXdef
  have hpos : 0 < Fintype.card ι₂ := Fintype.card_pos
  have h2ne : c₂ ≠ 0 := by
    rw [hc₂def, Finset.card_univ]
    exact_mod_cast hpos.ne'
  have h2top : c₂ ≠ ∞ := by rw [hc₂def]; finiteness
  have h1top : c₁ ≠ ∞ := by rw [hc₁def]; finiteness
  have hsum : ∑ q : ι₁ × ι₂, f q.1 = c₂ * X := by
    rw [Fintype.sum_prod_type, hXdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    show ∑ _y : ι₂, f i = c₂ * f i
    rw [Finset.sum_const, nsmul_eq_mul, hc₂def]
  have hcard : ((Finset.univ : Finset (ι₁ × ι₂)).card : ℝ≥0∞) = c₁ * c₂ := by
    rw [hc₁def, hc₂def]
    simp [Finset.card_univ, Fintype.card_prod]
  rw [hsum, hcard, ENNReal.mul_inv (Or.inr h2top) (Or.inl h1top)]
  calc c₁⁻¹ * c₂⁻¹ * (c₂ * X) = c₁⁻¹ * ((c₂⁻¹ * c₂) * X) := by ring
    _ = c₁⁻¹ * X := by rw [ENNReal.inv_mul_cancel h2ne h2top, one_mul]

/-- Product-index version: the local harmonic parent readout has the same
uniform fourth moment as on the overlap index. -/
theorem lintegral_nfProd_localReadout_four_le [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d)
    {ι : Type*} [Fintype ι] (hne : (Finset.univ : Finset ι).Nonempty)
    (centre : ι → Vec d) (mm : ℤ) (hh : 0 < h)
    (hp : vecNormSq p = 1) (hblock : (h : ℝ) ≤ M.delta⁻¹) :
    ∫⁻ omega, ((((Finset.univ : Finset ι).card : ℝ≥0∞)⁻¹) *
        ∑ i : ι, ENNReal.ofReal
          (oneStepNeumannDirichletAxisCoordinateSum M n h p (centre i) mm
            omega hh ^ (4 : ℕ))) ∂M.P.toMeasure ≤
      ENNReal.ofReal (16 * (d : ℝ) ^ (4 : ℕ) *
        oneStepSourceParentGradientConst ^ (4 : ℕ)) := by
  classical
  have hbase :=
    lintegral_average_oneStepNeumannDirichletAxisHarmonicGain_four_le
      (ι := ι) M n h p centre Finset.univ hne mm 0 hh hp hblock
  have hcongr : ∀ omega : NFSample d,
      (((Finset.univ : Finset ι).card : ℝ≥0∞)⁻¹) *
          ∑ i : ι, ENNReal.ofReal
            (oneStepNeumannDirichletAxisCoordinateSum M n h p (centre i) mm
              omega hh ^ (4 : ℕ)) =
        (((Finset.univ : Finset ι).card : ℝ≥0∞)⁻¹) *
          ∑ i : ι, ENNReal.ofReal
            (oneStepNeumannDirichletAxisHarmonicGain M n h p (centre i) mm 0
              omega hh ^ (4 : ℕ)) := by
    intro omega
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    unfold oneStepNeumannDirichletAxisHarmonicGain
    norm_num
  calc
    _ = ∫⁻ omega, ((((Finset.univ : Finset ι).card : ℝ≥0∞)⁻¹) *
        ∑ i : ι, ENNReal.ofReal
          (oneStepNeumannDirichletAxisHarmonicGain M n h p (centre i) mm 0
            omega hh ^ (4 : ℕ))) ∂M.P.toMeasure := lintegral_congr hcongr
    _ ≤ ENNReal.ofReal (16 * (d : ℝ) ^ (4 : ℕ) *
        oneStepSourceParentGradientConst ^ (4 : ℕ)) *
          ENNReal.ofReal (((3 : ℝ) ^ (-((0 : ℕ) : ℤ))) ^ (4 : ℕ)) := hbase
    _ = _ := by norm_num

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily
