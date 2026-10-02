import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNestedSourceParentReadout

/-!
# The finite-radius two-radius fold

The committed two-radius folds
`twoRadiusNeumann_four_le_delta_sixtyEight`
(`Section5Support/OneStepTwoRadiusNeumannMoments.lean`) and
`twoRadiusNeumannHessian_nested_thermodynamic_readout_le`
(`Section5Support/OneStepNestedSourceParentReadout.lean`) both remove the two
auxiliary harmonic radii *in the limit*: the first quantifies over all
`N₁ N₂` with a fixed observable `X`, the second sends the ambient volume to
infinity first.  Neither is usable at one fixed outer scale `K`, which is what
the fourth conjunct of `DualCellMajorantInputs` asks for.

This module replaces the limit by an explicit radius.  Since the harmonic
error `oneStepNestedHarmonicFourthError depth N` is dominated by the geometric
sequence `27 ^ (-N)`, choosing

```
  N ≥ nfFoldRadius depth delta = max (depth + 1) (68 * ceil |log delta / log 3|)
```

already puts both harmonic terms at the `delta ^ 68` level, so the fold closes
at a *single* radius with no passage to the limit and with a constant that is
still `delta`-independent.

Nothing here is thermodynamic and nothing here is specific to the Neumann
family: the input is any `OneStepTwoRadiusNeumannHessianFamily` together with
its three budgets.
-/

open MeasureTheory Homogenization
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-! ## The explicit radius -/

/-- The auxiliary harmonic radius at which the two-radius fold already closes
at the `delta ^ 68` level, without any limit.  The first branch keeps the
radius admissible for the Calderón--Zygmund interior depth; the second buys
the `delta ^ 68` gain. -/
def nfFoldRadius (depth : ℕ) (delta : ℝ) : ℕ :=
  max (depth + 1) (68 * ⌈|Real.log delta / Real.log 3|⌉₊)

theorem le_nfFoldRadius_left (depth : ℕ) (delta : ℝ) :
    depth + 1 ≤ nfFoldRadius depth delta :=
  le_max_left _ _

theorem le_nfFoldRadius_right (depth : ℕ) (delta : ℝ) :
    68 * ⌈|Real.log delta / Real.log 3|⌉₊ ≤ nfFoldRadius depth delta :=
  le_max_right _ _

/-- `3 ^ (-ceil |log delta / log 3|) ≤ delta` for `0 < delta ≤ 1`. -/
theorem three_inv_pow_ceil_le (delta : ℝ) (hdelta0 : 0 < delta)
    (hdelta1 : delta ≤ 1) :
    (3 : ℝ)⁻¹ ^ ⌈|Real.log delta / Real.log 3|⌉₊ ≤ delta := by
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hlogd : Real.log delta ≤ 0 := Real.log_nonpos hdelta0.le hdelta1
  have hlogb : |Real.log delta / Real.log 3| = Real.logb 3 delta⁻¹ := by
    rw [← Real.log_div_log, Real.log_inv,
      abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg hlogd hlog3.le)]
    ring
  have hceil : Real.logb 3 delta⁻¹ ≤
      (⌈|Real.log delta / Real.log 3|⌉₊ : ℝ) := by
    rw [← hlogb]
    exact Nat.le_ceil _
  have hinvle : delta⁻¹ ≤ (3 : ℝ) ^ ⌈|Real.log delta / Real.log 3|⌉₊ := by
    calc
      delta⁻¹ = (3 : ℝ) ^ (Real.logb 3 delta⁻¹) :=
        (Real.rpow_logb (by norm_num) (by norm_num)
          (inv_pos.mpr hdelta0)).symm
      _ ≤ (3 : ℝ) ^ ((⌈|Real.log delta / Real.log 3|⌉₊ : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hceil
      _ = (3 : ℝ) ^ ⌈|Real.log delta / Real.log 3|⌉₊ :=
        Real.rpow_natCast _ _
  rw [inv_pow, inv_le_comm₀ (by positivity) hdelta0]
  exact hinvle

/-- The real geometric bound behind the radius choice. -/
theorem three_inv_pow_three_mul_le_delta_pow_sixtyEight
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    {depth N : ℕ} (hN : nfFoldRadius depth delta ≤ N) :
    (3 : ℝ)⁻¹ ^ (3 * N) ≤ delta ^ (68 : ℕ) := by
  set c : ℕ := ⌈|Real.log delta / Real.log 3|⌉₊ with hc
  have hcN : c * 68 ≤ 3 * N := by
    have h68 : 68 * c ≤ N := le_trans (le_nfFoldRadius_right depth delta) hN
    omega
  calc
    (3 : ℝ)⁻¹ ^ (3 * N) ≤ (3 : ℝ)⁻¹ ^ (c * 68) := by
      apply pow_le_pow_of_le_one (by norm_num) (by norm_num) hcN
    _ = ((3 : ℝ)⁻¹ ^ c) ^ (68 : ℕ) := by rw [← pow_mul]
    _ ≤ delta ^ (68 : ℕ) :=
      pow_le_pow_left₀ (by positivity)
        (three_inv_pow_ceil_le delta hdelta0 hdelta1) 68

/-- **The radius choice.**  At any radius past `nfFoldRadius depth delta` the
literal nested harmonic fourth-moment error is already at the `delta ^ 68`
level. -/
theorem oneStepNestedHarmonicFourthError_le_ofReal_delta_pow_sixtyEight
    (depth : ℕ) {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    {N : ℕ} (hN : nfFoldRadius depth delta ≤ N) :
    oneStepNestedHarmonicFourthError depth N ≤
      ENNReal.ofReal (delta ^ (68 : ℕ)) := by
  have h3ne : (3 : ℝ≥0∞) ≠ 0 := by norm_num
  have h3top : (3 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hbase : (3 : ℝ≥0∞)⁻¹ ^ (4 : ℕ) * 3 = (3 : ℝ≥0∞)⁻¹ ^ (3 : ℕ) := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, mul_assoc,
      ENNReal.inv_mul_cancel h3ne h3top, mul_one]
  have hofReal : ((3 : ℝ≥0∞)⁻¹) = ENNReal.ofReal ((3 : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  calc
    oneStepNestedHarmonicFourthError depth N ≤
        ((3 : ℝ≥0∞)⁻¹ ^ (4 : ℕ) * 3) ^ N :=
      oneStepNestedHarmonicFourthError_le_geometric depth N
    _ = (3 : ℝ≥0∞)⁻¹ ^ (3 * N) := by rw [hbase, ← pow_mul]
    _ = ENNReal.ofReal ((3 : ℝ)⁻¹ ^ (3 * N)) := by
      rw [hofReal, ← ENNReal.ofReal_pow (by norm_num)]
    _ ≤ ENNReal.ofReal (delta ^ (68 : ℕ)) :=
      ENNReal.ofReal_le_ofReal
        (three_inv_pow_three_mul_le_delta_pow_sixtyEight hdelta0 hdelta1 hN)

/-! ## The fold at a single radius -/

/-- **Finite-radius two-radius fold.**  Reciprocal of
`twoRadiusNeumannHessian_thermodynamic_readout_le_delta_sixtyEight` with the
limit removed: at one fixed outer scale and one fixed auxiliary radius, once
the two harmonic errors are themselves at the `delta ^ 68` level the literal
Neumann readout is too. -/
theorem oneStepTwoRadiusNeumannHessianReadout_le_delta_sixtyEight_of_budgets
    {d : ℕ} {ι Omega : Type*} [DecidableEq ι] [MeasurableSpace Omega]
    {mu : Measure Omega} (s : Finset ι) (cell : ι → TriadicCube d)
    (F : OneStepTwoRadiusNeumannHessianFamily d ι Omega s cell)
    {delta CD C₁ C₂ err : ℝ≥0∞}
    (herr : err ≤ delta ^ (68 : ℕ))
    (hD : ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
        ∑ i ∈ s, ENNReal.ofReal
          ((F.toCellFamily.dirichlet i omega) ^ (4 : ℕ))) ∂mu ≤
      CD * delta ^ (68 : ℕ))
    (hH₁ : ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
        ∑ i ∈ s, ENNReal.ofReal
          ((F.toCellFamily.localHarmonic i omega) ^ (4 : ℕ))) ∂mu ≤
      C₁ * err)
    (hH₂ : ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
        ∑ i ∈ s, ENNReal.ofReal
          ((F.toCellFamily.outerHarmonic i omega) ^ (4 : ℕ))) ∂mu ≤
      C₂ * err) :
    oneStepTwoRadiusNeumannHessianReadout mu s cell F ≤
      (64 * (CD + C₁ + C₂)) * delta ^ (68 : ℕ) := by
  have hH₁' : ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
      ∑ i ∈ s, ENNReal.ofReal
        ((F.toCellFamily.localHarmonic i omega) ^ (4 : ℕ))) ∂mu ≤
      C₁ * delta ^ (68 : ℕ) :=
    hH₁.trans (by gcongr)
  have hH₂' : ∫⁻ omega, (((s.card : ℝ≥0∞)⁻¹) *
      ∑ i ∈ s, ENNReal.ofReal
        ((F.toCellFamily.outerHarmonic i omega) ^ (4 : ℕ))) ∂mu ≤
      C₂ * delta ^ (68 : ℕ) :=
    hH₂.trans (by gcongr)
  refine (oneStepTwoRadiusNeumannHessianReadout_le_of_budgets s cell F
    hD hH₁' hH₂').trans ?_
  ring_nf
  exact le_refl _

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold
