import SubdiffusiveProcess.Paper.prop_conc_uniform_prefix_moments

/-! # Uniform regularity prefixes with an infinite infrared field

The least prefix attained along arbitrarily large infrared cutoffs retains the
uniform exponential moment. This supplies a local regularity control only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology

namespace Paper
noncomputable section

/-- Infrared limiting prefixes retain the model-independent moment bound. -/
theorem prop_conc_uniform_infrared_prefix
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (t q : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d)
    (ht0 : 0 < t) (hq : 1 ≤ q) :
    ∃ delta0 B : ℝ, 0 < delta0 ∧ 0 < B ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M),
        M.delta ≤ delta0 →
        M.delta ≤ Sreg.C⁻¹ ∧ 1 - ((d : ℝ) - t) / 4 ∈ Sreg.alphaRange ∧
        ∀ z : SpatialCoordinates d, ∃ Lmac : ℕ → BilateralField d → ℕ,
          (∀ N, Measurable (Lmac N)) ∧
          (∀ N, eLpNorm (fun om => (3 : ℝ) ^ (t * (Lmac N om : ℝ)))
            (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B) ∧
          (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N L0 : ℕ,
            ∃ L' : ℕ, L0 ≤ L' ∧
              Sreg.prefixLen (N + L') (1 - ((d : ℝ) - t) / 4) N
                ((3 : ℝ) ^ N • z) (aux_aux_macro_moment_bank_relabel N om) ≤ Lmac N om) := by
  obtain ⟨delta0, A, rate, hdelta0, hA, hrate, htail⟩ :=
    aux_prop_conc_uniform_prefix_moments_tail d t q ht htd ht0 hq
  let lam : ℝ := q * t * Real.log 3
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hlam : 0 < lam := mul_pos (mul_pos hq0 ht0) (Real.log_pos (by norm_num))
  have hrate0 : 0 < rate := hlam.trans hrate
  let V : ℝ := A * Real.exp rate * (1 - Real.exp (-(rate - lam)))⁻¹
  have hden : 0 < 1 - Real.exp (-(rate - lam)) := by
    apply sub_pos.mpr
    apply Real.exp_lt_one_iff.mpr
    linarith only [hrate]
  have hV : 0 < V := mul_pos
    (mul_pos (zero_lt_one.trans_le hA) (Real.exp_pos _)) (inv_pos.mpr hden)
  refine ⟨delta0, V ^ (1 / q), hdelta0, Real.rpow_pos_of_pos hV _, ?_⟩
  intro M Sreg hdelta
  obtain ⟨hdeltaC, halpha, htM⟩ := htail M Sreg hdelta
  refine ⟨hdeltaC, halpha, ?_⟩
  intro z
  let f : ℕ → ℕ → BilateralField d → ℕ := fun N L' om =>
    Sreg.prefixLen (N + L') (1 - ((d : ℝ) - t) / 4) N ((3 : ℝ) ^ N • z)
      (aux_aux_macro_moment_bank_relabel N om)
  have hfmeas (N L' : ℕ) : Measurable (f N L') :=
    (Sreg.prefix_measurable _ _ _ _).comp
      (aux_aux_macro_moment_bank_relabel_measurePreserving M N).measurable
  let T : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (A * Real.exp (-rate * k))
  have hftail (N k L' : ℕ) : (chaosSampleLaw M).toMeasure {om | k < f N L' om} ≤ T k := by
    have hpres := aux_aux_macro_moment_bank_relabel_measurePreserving M N
    change (chaosSampleLaw M).toMeasure (aux_aux_macro_moment_bank_relabel N ⁻¹'
      {om | k < Sreg.prefixLen (N + L') (1 - ((d : ℝ) - t) / 4) N
        ((3 : ℝ) ^ N • z) om}) ≤ T k
    rw [hpres.measure_preimage
      (measurableSet_lt measurable_const (Sreg.prefix_measurable _ _ _ _)).nullMeasurableSet]
    exact htM _ _ _ _
  have hT0 : Tendsto T atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    apply ENNReal.tendsto_ofReal
    have hpows := tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-rate)).le
      (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hrate0))
    have hexp : Tendsto (fun k : ℕ => Real.exp (-rate * k)) atTop (𝓝 0) := by
      convert hpows using 1
      ext k
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    simpa only [mul_zero] using hexp.const_mul A
  let Lmac := fun N => aux_aux_macro_moment_bank_ioBound (f N)
  have hm (N : ℕ) : Measurable (Lmac N) :=
    aux_aux_macro_moment_bank_ioBound_measurable (f N) (hfmeas N)
  refine ⟨Lmac, hm, ?_, ?_⟩
  · intro N
    have hio (k : ℕ) : (chaosSampleLaw M).toMeasure {om | k < Lmac N om} ≤ T k :=
      aux_aux_macro_moment_bank_measure_lt_ioBound_le _ (f N) k (T k) (hftail N k)
    have hmoment := aux_aux_macro_moment_bank_lintegral_exp_le
      (chaosSampleLaw M).toMeasure (Lmac N) (hm N) A rate lam hA hlam.le hrate hio
    exact (aux_aux_macro_moment_bank_eLpNorm_rpow_three_le
      (chaosSampleLaw M).toMeasure (Lmac N) t q hq0 V hmoment).trans_eq
      (ENNReal.ofReal_rpow_of_nonneg hV.le (by positivity))
  · rw [ae_all_iff]
    intro N
    exact aux_aux_macro_moment_bank_ae_ioBound_attained _ (f N) T
      (fun k L' => hftail N k L') hT0

end
end Paper
