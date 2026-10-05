module

public import SubdiffusiveProcess.Section10.ChaosVagueMartingale
public import SubdiffusiveProcess.MultiplicativeChaos.TailNull

@[expose] public section

/-! Uniform open-set bounds pass to the actual locally finite vague limit.
The second helper removes the infrared weight on a fixed compact window. -/

open MeasureTheory SubdiffusiveProcess Filter Topology TopologicalSpace Set
open scoped ENNReal CompactlySupported

noncomputable section
namespace SubdiffusiveProcess.Section10

/-- A cutoff bound on an open set passes to the same vague limit. -/
theorem open_mass_le_of_same_vague_limit {d : ℕ}
    (muN : ℕ → Measure (SpatialCoordinates d)) (mu : Measure (SpatialCoordinates d))
    (hN : ∀ n, IsLocallyFiniteMeasure (muN n)) [IsLocallyFiniteMeasure mu]
    (hc : MeasuresConvergeLocally muN mu) (U : Set (SpatialCoordinates d))
    (hU : IsOpen U) (B : ℝ≥0∞) (hb : ∀ n, muN n U ≤ B) : mu U ≤ B := by
  have htest (n : ℕ) : (∫⁻ x, ENNReal.ofReal (urysohnSeq hU n x) ∂mu) ≤ B := by
    apply le_of_tendsto
      (_root_.SubdiffusiveProcess.Paper.aux_lim_measure_vague_positive_lintegral muN mu hN hc
        (urysohnSeq hU n) (urysohnSeq_nonneg hU n))
    refine Eventually.of_forall fun k => le_trans ?_ (hb k)
    calc (∫⁻ x, ENNReal.ofReal (urysohnSeq hU n x) ∂muN k)
        ≤ ∫⁻ x, U.indicator (fun _ => (1 : ℝ≥0∞)) x ∂muN k := by
          apply lintegral_mono
          intro x
          by_cases hx : x ∈ U
          · rw [Set.indicator_of_mem hx]
            exact (ENNReal.ofReal_le_ofReal ((urysohnSeq_spec hU n).1 x).2).trans_eq
              ENNReal.ofReal_one
          · rw [Set.indicator_of_notMem hx]
            have hf : urysohnSeq hU n x = 0 := by
              by_contra hn
              exact hx ((urysohnSeq_spec hU n).2.2 (subset_tsupport _ hn))
            simp [hf]
      _ = muN k U := by rw [lintegral_indicator_const hU.measurableSet, one_mul]
  rw [← iUnion_openPiece hU, (monotone_openPiece U).measure_iUnion]
  refine iSup_le fun n => le_trans ?_ (htest n)
  calc mu (openPiece U n)
      = ∫⁻ x, (openPiece U n).indicator (fun _ => (1 : ℝ≥0∞)) x ∂mu := by
          rw [lintegral_indicator_const (isClosed_openPiece U n).measurableSet, one_mul]
    _ ≤ ∫⁻ x, ENNReal.ofReal (urysohnSeq hU n x) ∂mu := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ openPiece U n
        · simp [hx, (urysohnSeq_spec hU n).2.1 x hx]
        · simp [hx]

/-- On a compact window, the inverse infrared weight is bounded by its
compact exponential envelope, for the literal weighted measure. -/
theorem mass_le_compact_envelope_mul_weighted {d : ℕ}
    (mu : Measure (SpatialCoordinates d)) (h : C(SpatialCoordinates d, ℝ))
    (K : Compacts (SpatialCoordinates d)) (U : Set (SpatialCoordinates d))
    (hU : MeasurableSet U) (hUK : U ⊆ K) :
    mu U ≤ ENNReal.ofReal (Real.exp ‖h.restrict (K : Set (SpatialCoordinates d))‖) *
      (mu.withDensity (fun x => ENNReal.ofReal (Real.exp (h x)))) U := by
  rw [withDensity_apply _ hU, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc mu U = ∫⁻ _x, (1 : ℝ≥0∞) ∂mu.restrict U := by simp
    _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp ‖h.restrict (K : Set (SpatialCoordinates d))‖) *
          ENNReal.ofReal (Real.exp (h x)) ∂mu.restrict U := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hU] with x hx
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      apply Real.one_le_exp_iff.mpr
      have hh := ContinuousMap.norm_coe_le_norm
        (h.restrict (K : Set (SpatialCoordinates d))) ⟨x, hUK hx⟩
      change ‖h x‖ ≤ _ at hh
      rw [Real.norm_eq_abs] at hh
      linarith [neg_abs_le (h x)]

end SubdiffusiveProcess.Section10
