module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventExitUpperMean

@[expose] public section

/-! Discounted unit occupation in the original clock. Finiteness is automatic
at a positive discount; monotone convergence needs no zero-mass identification. -/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventExitUpper
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Section10

/-- Unnormalized discounted unit occupation, in ENNReal semantics. -/
def discountedUnitOccupation {d : ℕ} (law : Kernel (Vec d) (Path d))
    (U : Set (Vec d)) (s : ℝ) (x : Vec d) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t / s)) *
    law x {w | ENNReal.ofReal t < LifetimePath.exitTime U w}

lemma measurable_unitSurvival {d : ℕ} (law : Kernel (Vec d) (Path d))
    [IsMarkovKernel law] {U : Set (Vec d)} (hU : IsOpen U) (x : Vec d) :
    Measurable (fun t : ℝ => law x {w | ENNReal.ofReal t < LifetimePath.exitTime U w}) := by
  have h := (killedKernel_joint_measurable law U hU univ MeasurableSet.univ).comp
    (measurable_real_toNNReal.prodMk (measurable_const (a := x)))
  simpa only [Function.comp_def, killedKernel_univ_eq_survival hU] using! h

/-- Every positive-discount occupation is finite, at every start. -/
theorem discountedUnitOccupation_le_scale {d : ℕ} (law : Kernel (Vec d) (Path d))
    [IsMarkovKernel law] (U : Set (Vec d)) {s : ℝ} (hs : 0 < s) (x : Vec d) :
    discountedUnitOccupation law U s x ≤ ENNReal.ofReal s := by
  have he : ∀ t : ℝ, -t / s = -(s⁻¹ * t) := by intro t; simp only [div_eq_mul_inv]; ring
  calc
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t / s)) := by
      apply lintegral_mono
      intro t
      exact (mul_le_mul' le_rfl (prob_le_one (μ := law x))).trans_eq (mul_one _)
    _ = ENNReal.ofReal s := by
      simp_rw [he]
      simpa only [one_mul, inv_inv] using!
        lintegral_Ioi_ofReal_exp_neg_mul (K := 1) zero_le_one (inv_pos.mpr hs)

/-- The source normalized resolvent is precisely s^-1 times unit occupation. -/
theorem discountedUnitOccupation_eq_ofReal_scaled_resolvent {d : ℕ}
    (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    {U : Set (Vec d)} (hU : IsOpen U) {s : ℝ} (hs : 0 < s) (x : Vec d) :
    discountedUnitOccupation law U s x =
      ENNReal.ofReal (s * killedResolvent law U s (fun _ => 1) x) := by
  let S : ℝ → ℝ≥0∞ := fun t => law x {w | ENNReal.ofReal t < LifetimePath.exitTime U w}
  have hS : Measurable S := measurable_unitSurvival law hU x
  have hSf (t : ℝ) : S t ≠ ⊤ := (lt_of_le_of_lt prob_le_one ENNReal.one_lt_top).ne
  let g : ℝ → ℝ := fun t => Real.exp (-t / s) * (S t).toReal
  have hg : Measurable g :=
    (Real.measurable_exp.comp (measurable_id.neg.div_const s)).mul hS.ennreal_toReal
  have hg0 (t : ℝ) : 0 ≤ g t := mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg
  have hge (t : ℝ) : ‖g t‖ ≤ Real.exp (-t / s) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 t)]
    exact (mul_le_mul_of_nonneg_left (ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa only [ENNReal.ofReal_one] using! (prob_le_one (μ := law x) (s := {w | ENNReal.ofReal t < LifetimePath.exitTime U w}))))
      (Real.exp_pos _).le).trans_eq (mul_one _)
  have he : ∀ t : ℝ, -t / s = -(s⁻¹ * t) := by intro t; simp only [div_eq_mul_inv]; ring
  have hint : IntegrableOn g (Ioi 0) := by
    refine Integrable.mono' ?_ hg.aestronglyMeasurable (Filter.Eventually.of_forall hge)
    simpa only [he, neg_mul] using! exp_neg_integrableOn_Ioi (0 : ℝ) (inv_pos.mpr hs)
  have hid : ENNReal.ofReal (∫ t in Ioi (0 : ℝ), g t) =
      discountedUnitOccupation law U s x := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hg0)]
    apply lintegral_congr
    intro t
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal (hSf t)]
  rw [← hid]
  congr 1
  unfold killedResolvent
  rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by simp [g, S, Measure.real]

private lemma iSup_unitDiscount (t : ℝ) (ht : 0 ≤ t) :
    ⨆ n : ℕ, ENNReal.ofReal (Real.exp (-t / ((n : ℝ) + 1))) = 1 := by
  have hmono : Monotone fun n : ℕ => ENNReal.ofReal (Real.exp (-t / ((n : ℝ) + 1))) := by
    intro m n hmn
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    simp only [div_eq_mul_inv, neg_mul]
    apply neg_le_neg
    exact mul_le_mul_of_nonneg_left
      (inv_anti₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)
        (add_le_add (Nat.cast_le.mpr hmn) (le_refl (1 : ℝ)))) ht
  have hzero : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [one_div] using! h
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-t / ((n : ℝ) + 1))))
      atTop (𝓝 1) := by
    have hreal := (Real.continuous_exp.tendsto _).comp (hzero.const_mul (-t))
    simpa only [div_eq_mul_inv, mul_zero, Real.exp_zero, ENNReal.ofReal_one, Function.comp_def] using!
      ENNReal.tendsto_ofReal hreal
  exact tendsto_nhds_unique (tendsto_atTop_iSup hmono) hlim

/-- Monotone convergence identifies the unnormalized mean with the discounted supremum. -/
theorem meanExit_eq_iSup_discountedUnitOccupation {d : ℕ}
    (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    {U : Set (Vec d)} (hU : IsOpen U) (x : Vec d) :
    meanExit law U x = ⨆ n : ℕ, discountedUnitOccupation law U ((n : ℝ) + 1) x := by
  let S : ℝ → ℝ≥0∞ := fun t => law x {w | ENNReal.ofReal t < LifetimePath.exitTime U w}
  have hS : Measurable S := measurable_unitSurvival law hU x
  have hm : ∀ n : ℕ, Measurable (fun t : ℝ =>
      ENNReal.ofReal (Real.exp (-t / ((n : ℝ) + 1))) * S t) := fun n =>
    (Real.measurable_exp.comp (measurable_id.neg.div_const _)).ennreal_ofReal.mul hS
  have hmono : ∀ t ∈ Ioi (0 : ℝ), Monotone (fun n : ℕ =>
      ENNReal.ofReal (Real.exp (-t / ((n : ℝ) + 1))) * S t) := by
    intro t ht m n hmn
    apply mul_le_mul_left
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    simp only [div_eq_mul_inv, neg_mul]
    apply neg_le_neg
    exact mul_le_mul_of_nonneg_left
      (inv_anti₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)
        (add_le_add (Nat.cast_le.mpr hmn) (le_refl (1 : ℝ)))) ht.le
  rw [meanExit_eq_lintegral_survival law hU x]
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ⨆ n : ℕ,
        ENNReal.ofReal (Real.exp (-t / ((n : ℝ) + 1))) * S t := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change S t = ⨆ n : ℕ, ENNReal.ofReal (Real.exp (-t / ((n : ℝ) + 1))) * S t
      rw [← ENNReal.iSup_mul, iSup_unitDiscount t ht.le, one_mul]
    _ = _ := lintegral_iSup' (fun n => (hm n).aemeasurable)
      (ae_restrict_of_forall_mem measurableSet_Ioi hmono)

/-- A bound uniform in positive discount bounds the actual unnormalized mean. -/
theorem meanExit_le_of_discountedUnitOccupation_le {d : ℕ}
    (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    {U : Set (Vec d)} (hU : IsOpen U) (x : Vec d) {B : ℝ≥0∞}
    (hbound : ∀ n : ℕ, discountedUnitOccupation law U ((n : ℝ) + 1) x ≤ B) :
    meanExit law U x ≤ B := by
  rw [meanExit_eq_iSup_discountedUnitOccupation law hU x]
  exact iSup_le hbound

end SubdiffusiveProcess.Section10
