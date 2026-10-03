module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellGauge

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored

open Homogenization Homogenization.IndependentSums MeasureTheory
open SubdiffusiveProcess.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-! ## The summable own-scale gauge sequence -/

/-- The own-scale gauge of shell `k`, discounted by the shell's own scale. -/
def shellScaledGauge (k : ℕ) (omega : PotentialSample d) : ℝ :=
  (((3 : ℝ) ^ k)⁻¹) * shellUnitGauge k omega

theorem shellScaledGauge_nonneg (k : ℕ) (omega : PotentialSample d) :
    0 ≤ shellScaledGauge k omega :=
  mul_nonneg (by positivity) (shellUnitGauge_nonneg k omega)

private theorem summable_inv_pow_three_mul (c : ℝ) :
    Summable fun k : ℕ => (((3 : ℝ) ^ k)⁻¹) * c := by
  have hgeom : Summable fun k : ℕ => ((3 : ℝ)⁻¹) ^ k :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine (hgeom.mul_right c).congr fun k => ?_
  rw [inv_pow]

/-- The disorder scale is positive, in the exact form the `Γ₂` gauges carry. -/
private theorem gammaTwoShellScale_pos (M : GMCModel d) :
    0 < (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta := by
  have hlog : 0 < 1 + Real.log 2 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  exact mul_pos (Real.rpow_pos_of_pos hlog _) M.shellPrefix.delta_pos

/-- The single probabilistic input: almost surely the discounted own-scale
gauges are summable. -/
theorem ae_summable_shellScaledGauge (M : GMCModel d) :
    ∀ᵐ omega ∂M.P.toMeasure, Summable fun k => shellScaledGauge k omega := by
  have hscale := gammaTwoShellScale_pos M
  refine ae_summable_of_isBigOWith_gammaSigma
    (μ := M.P.toMeasure) (X := fun k => shellScaledGauge (d := d) k)
    (a := fun k => (((3 : ℝ) ^ k)⁻¹) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta))
    (sigma := 2) (by norm_num) (fun k omega => shellScaledGauge_nonneg k omega)
    (fun k => ((measurable_shellUnitGauge k).const_mul _).aemeasurable)
    (fun k => by positivity) (summable_inv_pow_three_mul _) fun k => ?_
  exact (isBigOWith_gammaTwo_shellUnitGauge M k).const_mul (by positivity)

/-! ## The deterministic passage to `ShellC11Summable` -/

/-- Below the start index the carrier's own compact-set data already supplies a
finite constant for all three gauges at once. -/
private theorem exists_compact_shell_constant (omega : PotentialSample d)
    (R : ℝ) (k : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧
      (∀ x ∈ Metric.closedBall (0 : Vec d) R, |omega k x - omega k 0| ≤ c) ∧
      (∀ x ∈ Metric.closedBall (0 : Vec d) R,
        ‖PotentialField.deriv (omega k) x‖ ≤ c) ∧
      (∀ x ∈ Metric.closedBall (0 : Vec d) R,
        ∀ y ∈ Metric.closedBall (0 : Vec d) R,
        ‖PotentialField.deriv (omega k) x - PotentialField.deriv (omega k) y‖ ≤
          c * ‖x - y‖) := by
  obtain ⟨c1, hc1⟩ := (isCompact_closedBall (0 : Vec d) R).exists_bound_of_continuousOn
    (((omega k).1.1.continuous.sub continuous_const).continuousOn)
  obtain ⟨c2, hc2⟩ := (isCompact_closedBall (0 : Vec d) R).exists_bound_of_continuousOn
    ((PotentialField.deriv (omega k)).continuous.continuousOn)
  obtain ⟨c3, hc3⟩ := (omega k).2.2 (Metric.closedBall (0 : Vec d) R)
    (isCompact_closedBall _ _)
  refine ⟨max 0 (max c1 (max c2 (c3 : ℝ))), le_max_left _ _, ?_, ?_, ?_⟩
  · intro x hx
    have h1 : |omega k x - omega k 0| ≤ c1 := by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using! hc1 x hx
    exact h1.trans ((le_max_left c1 _).trans (le_max_right 0 _))
  · intro x hx
    exact (hc2 x hx).trans
      (((le_max_left c2 _).trans (le_max_right c1 _)).trans (le_max_right 0 _))
  · intro x hx y hy
    have hlip := hc3.dist_le_mul x hx y hy
    rw [dist_eq_norm, dist_eq_norm] at hlip
    refine hlip.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact ((le_max_right c2 _).trans (le_max_right c1 _)).trans (le_max_right 0 _)

/-- Summability of the discounted own-scale gauges gives the full
`C¹ˑ¹` shell package on every closed ball. -/
theorem shellC11Summable_of_summable {omega : PotentialSample d}
    (h : Summable fun k => shellScaledGauge k omega) : ShellC11Summable omega := by
  intro R
  set R' : ℝ := max R 0 with hR'_def
  have hR' : 0 ≤ R' := le_max_right R 0
  have hsub : Metric.closedBall (0 : Vec d) R ⊆ Metric.closedBall (0 : Vec d) R' :=
    Metric.closedBall_subset_closedBall (le_max_left R 0)
  obtain ⟨K, hK⟩ := exists_shellStart R'
  choose c hc0 hcu hcv hcw using exists_compact_shell_constant omega R'
  set s : ℕ → ℝ := fun k =>
    (R' + 1) * shellScaledGauge k omega + (if k < K then c k else 0) with hs_def
  have hbase : ∀ k, 0 ≤ shellScaledGauge k omega := fun k =>
    shellScaledGauge_nonneg k omega
  have hif : ∀ k : ℕ, 0 ≤ (if k < K then c k else 0) := by
    intro k
    by_cases hk : k < K <;> simp [hk, hc0 k]
  have hs_nonneg : ∀ k, 0 ≤ s k := fun k =>
    add_nonneg (mul_nonneg (by linarith) (hbase k)) (hif k)
  have hs_summable : Summable s := by
    refine (h.mul_left (R' + 1)).add ?_
    refine summable_of_ne_finset_zero (s := Finset.range K) fun k hk => ?_
    rw [if_neg (by simpa using hk)]
  -- the two regimes
  have hbig : ∀ k : ℕ, K ≤ k → shellScaledGauge k omega ≤ s k := by
    intro k _
    have := hif k
    nlinarith [hbase k]
  have hsmall : ∀ k : ℕ, k < K → c k ≤ s k := by
    intro k hk
    have hb : 0 ≤ (R' + 1) * shellScaledGauge k omega :=
      mul_nonneg (by linarith) (hbase k)
    simp only [hs_def, if_pos hk]
    linarith
  refine ⟨s, s, s, hs_nonneg, hs_nonneg, hs_nonneg, hs_summable, hs_summable,
    hs_summable, ?_, ?_, ?_⟩
  · intro k x hx
    rcases lt_or_ge k K with hk | hk
    · exact (hcu k x (hsub hx)).trans (hsmall k hk)
    · refine (abs_sub_origin_le_shellUnitGauge hR' (hK k hk) (hsub hx)).trans ?_
      have hb := hbase k
      have hif' := hif k
      have hRle : R ≤ R' := le_max_left R 0
      simp only [hs_def, shellScaledGauge] at *
      nlinarith
  · intro k x hx
    rcases lt_or_ge k K with hk | hk
    · exact (hcv k x (hsub hx)).trans (hsmall k hk)
    · exact (norm_deriv_le_shellUnitGauge (hK k hk) (hsub hx)).trans (hbig k hk)
  · intro k x hx y hy
    rcases lt_or_ge k K with hk | hk
    · exact (hcw k x (hsub hx) y (hsub hy)).trans
        (mul_le_mul_of_nonneg_right (hsmall k hk) (norm_nonneg _))
    · refine (norm_deriv_sub_deriv_le_shellUnitGauge (hK k hk) (hsub hx)
        (hsub hy)).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      have hinv : (((3 : ℝ) ^ k)⁻¹) ≤ 1 := by
        rw [inv_le_one_iff₀]
        right
        exact one_le_pow₀ (by norm_num)
      have hb := hbase k
      have hg := shellUnitGauge_nonneg k omega
      have hif' := hif k
      simp only [hs_def, shellScaledGauge] at *
      nlinarith

/-! ## The full-measure conclusion -/

theorem ae_shellC11Summable (M : GMCModel d) :
    ∀ᵐ omega ∂M.P.toMeasure, ShellC11Summable omega :=
  (ae_summable_shellScaledGauge M).mono fun _ h => shellC11Summable_of_summable h

theorem ae_mem_anchoredC11GoodSet (M : GMCModel d) :
    ∀ᵐ omega ∂M.P.toMeasure, omega ∈ anchoredC11GoodSet d :=
  (ae_shellC11Summable M).mono fun _ h => mem_anchoredC11GoodSet_of_shellC11Summable h

/-- The canonical anchored good event has full measure.  Measurability of the
event is *not* used: `Measure` is an outer measure, so the union bound on
`S ∪ Sᶜ = univ` suffices. -/
theorem measure_anchoredC11GoodSet_eq_one (M : GMCModel d) :
    M.P.toMeasure (anchoredC11GoodSet d) = 1 := by
  have hcompl : M.P.toMeasure ((anchoredC11GoodSet d)ᶜ) = 0 :=
    ae_iff.mp (ae_mem_anchoredC11GoodSet M)
  have hunion : M.P.toMeasure (anchoredC11GoodSet d ∪ (anchoredC11GoodSet d)ᶜ) ≤
      M.P.toMeasure (anchoredC11GoodSet d) +
        M.P.toMeasure ((anchoredC11GoodSet d)ᶜ) :=
    measure_union_le (μ := M.P.toMeasure) (anchoredC11GoodSet d)
      ((anchoredC11GoodSet d)ᶜ)
  rw [Set.union_compl_self, measure_univ, hcompl, add_zero] at hunion
  have hupper : M.P.toMeasure (anchoredC11GoodSet d) ≤ 1 := by
    have hmono := measure_mono (μ := M.P.toMeasure)
      (Set.subset_univ (anchoredC11GoodSet d))
    rwa [measure_univ] at hmono
  exact le_antisymm hupper hunion

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
