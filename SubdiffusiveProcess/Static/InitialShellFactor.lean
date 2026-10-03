module

public import SubdiffusiveProcess.Static.SubscaleCubeMoments
public import SubdiffusiveProcess.Section9.CutoffInitialMass

@[expose] public section

/-! # A two-sided factor on a microscopic cube -/
open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Frozen.Assumptions
open Homogenization hiding Vec TriadicCube
open SubdiffusiveProcess.Static
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

/-- One initial-shell factor controls the coefficient and its inverse. -/
def initialShellFactor {d : ℕ} (M : GMCModel d) (ω : PotentialSample d) : ℝ :=
  Real.exp (translatedShellG2 0 0 ω + tauSq M.P)

theorem measurable_initialShellFactor {d : ℕ} (M : GMCModel d) :
    Measurable (initialShellFactor M) :=
  ((measurable_translatedShellG2 0 0).add_const _).exp

theorem one_le_initialShellFactor {d : ℕ} (M : GMCModel d) (ω : PotentialSample d) :
    1 ≤ initialShellFactor M ω :=
  Real.one_le_exp (add_nonneg (translatedShellG2_nonneg _ _ _) M.G4.tauSq_pos.le)

theorem initialShellFactor_bounds {d : ℕ} (M : GMCModel d) (ω : PotentialSample d)
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d 0)) :
    aCutoff M 0 ω x ≤ initialShellFactor M ω ∧
      (aCutoff M 0 ω x)⁻¹ ≤ initialShellFactor M ω := by
  have hxg := SubdiffusiveProcess.Section9.abs_potentialShell_le_translatedShellG2_on_originCube ω hx
  have ht := M.G4.tauSq_pos.le
  simp only [aCutoff, Nat.zero_add, Finset.sum_range_one, initialShellFactor]
  constructor
  · apply Real.exp_le_exp.mpr
    linarith only [(abs_le.mp hxg).2, ht]
  · rw [← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    linarith only [(abs_le.mp hxg).1]

/-- Every prescribed moment is bounded independently of the model. -/
theorem initialShellFactor_moment_bound (d : ℕ) (q : ℝ) (hq : 0 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : GMCModel d,
      (∫⁻ ω, ENNReal.ofReal (initialShellFactor M ω ^ q) ∂M.P.toMeasure) ≤
        ENNReal.ofReal C := by
  let α : ℝ := (1 + Real.log 2) ^ (2 : ℝ)⁻¹
  have hα : 0 < α := by
    dsimp only [α]
    apply Real.rpow_pos_of_pos
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  let C := 4 * Real.exp (q ^ 2 * (α / 2) ^ 2 / 2 + q * (Real.log 2 / 8))
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro M
  have hA : 0 < α * M.delta := mul_pos hα M.shellPrefix.delta_pos
  have hg : Homogenization.IndependentSums.IsBigO M.P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 2) (translatedShellG2 0 0) (α * M.delta) := by
    simpa only [Homogenization.IndependentSums.IsBigO,
      abs_of_nonneg (translatedShellG2_nonneg _ _ _), α] using
      isBigOWith_gammaTwo_translatedShellG2 M 0 0
  obtain ⟨hi, hb⟩ := integral_exp_abs_sub_const_le (b := -tauSq M.P) hA hq
    (measurable_translatedShellG2 0 0).aemeasurable hg
  have heq : (fun ω => Real.exp (q * |translatedShellG2 0 0 ω - -tauSq M.P|)) =
      fun ω => initialShellFactor M ω ^ q := by
    funext ω
    rw [sub_neg_eq_add, abs_of_nonneg
      (add_nonneg (translatedShellG2_nonneg _ _ _) M.G4.tauSq_pos.le)]
    simp only [initialShellFactor, ← Real.exp_mul, mul_comm]
  rw [heq] at hi hb
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun ω => by unfold initialShellFactor; positivity)]
  apply ENNReal.ofReal_le_ofReal
  refine hb.trans ?_
  dsimp only [C]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  have hAmax : α * M.delta ≤ α / 2 := by nlinarith only [M.shellPrefix.delta_le_half, hα]
  have hAsq := pow_le_pow_left₀ hA.le hAmax 2
  have ht : tauSq M.P ≤ Real.log 2 / 8 := by
    have hδsq := pow_le_pow_left₀ M.shellPrefix.delta_pos.le M.shellPrefix.delta_le_half 2
    have ht0 := tauSq_le_delta_sq M
    have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    nlinarith only [ht0, hδsq, hlog]
  rw [abs_neg, abs_of_nonneg M.G4.tauSq_pos.le]
  nlinarith only [hAsq, ht, hq, sq_nonneg q]

end SubdiffusiveProcess.Static
