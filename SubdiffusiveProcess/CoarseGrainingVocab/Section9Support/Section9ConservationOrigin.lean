module

public import SubdiffusiveProcess.Section9.PointwiseStrongLaw

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open Homogenization hiding Vec
open Filter Topology MeasureTheory SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored

theorem bddAbove_exp_centered_of_average_tendsto {u : ℕ → ℝ} {tau : ℝ}
    (htau : 0 < tau)
    (hu : Tendsto (fun n ↦ u n / ((n : ℝ) + 1)) atTop (nhds 0)) :
    BddAbove (Set.range (fun n ↦ Real.exp (u n - ((n : ℝ) + 1) * tau))) := by
  refine Filter.IsBoundedUnder.bddAbove_range ⟨1, ?_⟩
  change ∀ᶠ n in atTop, Real.exp (u n - ((n : ℝ) + 1) * tau) ≤ 1
  have key : ∀ᶠ n in atTop, u n / ((n : ℝ) + 1) ≤ tau := by
    filter_upwards [hu.eventually_lt_const htau] with n hn
    exact le_of_lt hn
  filter_upwards [key] with n hn
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [Real.exp_le_one_iff]
  rw [div_le_iff₀ hpos] at hn
  nlinarith

theorem aCutoff_origin_eq_exp_centered {d : ℕ} (M : GMCModel d)
    (omega : PotentialSample d) (L : ℕ) :
    aCutoff M L omega 0 = Real.exp
      ((∑ k ∈ Finset.range (L + 1), omega k 0) - ((L : ℝ) + 1) * tauSq M.P) := by
  rw [aCutoff]
  congr 1
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [Nat.cast_add, Nat.cast_one]

theorem measurable_cutoffOriginSup {d : ℕ} (M : GMCModel d) :
    Measurable (supEnvelope (fun L : ℕ ↦
      fun omega : AnchoredC11Sample d ↦ aCutoff M L omega.val 0)) := by
  apply measurable_supEnvelope
  intro L
  exact (measurable_aCutoff M L 0).comp measurable_subtype_coe

/-- Almost surely, the measurable supremum is finite and dominates every
finite cutoff at the origin. -/
theorem ae_aCutoff_origin_le_supEnvelope {d : ℕ} (M : GMCModel d) :
    ∀ᵐ omega ∂(anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
      (measure_anchoredC11GoodSet_eq_one M)).toMeasure,
      ∀ L, aCutoff M L omega.val 0 ≤
        supEnvelope (fun n : ℕ ↦
          fun eta : AnchoredC11Sample d ↦ aCutoff M n eta.val 0) omega := by
  apply ae_forall_le_supEnvelope
  filter_upwards [SubdiffusiveProcess.Section9.ae_tendsto_pointwiseShellAverage_zero_anchored M]
    with omega homega
  obtain ⟨C, hC⟩ := bddAbove_exp_centered_of_average_tendsto M.G4.tauSq_pos homega
  refine ⟨C, fun L ↦ ?_⟩
  rw [aCutoff_origin_eq_exp_centered]
  exact hC ⟨L, rfl⟩

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
