import SubdiffusiveProcess.Paper.aux_macro_moment_bank

/-! # Uniform moments of the regularity prefix

A fixed lower bound for the geometric tail rate gives prefix moments with the
constant chosen before the model. This does not assert response concentration.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology

namespace Paper
noncomputable section

/-- The regularity-prefix tail admits a fixed decay rate independent of the model. -/
theorem aux_prop_conc_uniform_prefix_moments_tail
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (t q : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d)
    (ht0 : 0 < t) (hq : 1 ≤ q) :
    ∃ delta0 A rate : ℝ, 0 < delta0 ∧ 1 ≤ A ∧ q * t * Real.log 3 < rate ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M),
        M.delta ≤ delta0 →
        M.delta ≤ Sreg.C⁻¹ ∧ 1 - ((d : ℝ) - t) / 4 ∈ Sreg.alphaRange ∧
        ∀ (L m : ℕ) (y : SpatialCoordinates d) (n : ℕ),
          (chaosSampleLaw M).toMeasure
            {om | n < Sreg.prefixLen L (1 - ((d : ℝ) - t) / 4) m y om} ≤
              ENNReal.ofReal (A * Real.exp (-rate * n)) := by
  let Cd : ℝ := ((d : ℝ) + 1) ^ 2 *
    max 1 (Classical.choose (SubdiffusiveProcess.Frozen.Section6.cutoff_holder_regularity d))
  have hCd1 : 1 ≤ Cd := by
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hc : 1 ≤ max 1 (Classical.choose
        (SubdiffusiveProcess.Frozen.Section6.cutoff_holder_regularity d)) := le_max_left _ _
    have hs : 1 ≤ ((d : ℝ) + 1) ^ 2 := by nlinarith only [hd0]
    exact one_le_mul_of_one_le_of_one_le hs hc
  let lam : ℝ := q * t * Real.log 3
  let rate : ℝ := 2 * q * t * Real.log 3
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hlam : 0 < lam := mul_pos (mul_pos hq0 ht0) (Real.log_pos (by norm_num))
  have hrate : lam < rate := by dsimp [rate, lam]; nlinarith only [hlam]
  have hrate0 : 0 ≤ rate := hlam.le.trans hrate.le
  let A : ℝ := Cd * Real.exp (rate * Cd)
  have hA : 1 ≤ A := one_le_mul_of_one_le_of_one_le hCd1
    (Real.one_le_exp (mul_nonneg hrate0 (zero_le_one.trans hCd1)))
  obtain ⟨delta0, hdelta0, hthreshold⟩ :=
    aux_aux_macro_moment_bank_threshold t q ht htd ht0.le hq
  refine ⟨delta0, A, rate, hdelta0, hA, hrate, ?_⟩
  intro M Sreg hdelta
  obtain ⟨hdeltaC, halpha, hrateM⟩ := hthreshold M Sreg hdelta
  have hCeq : Sreg.C = Cd := Sreg.C_eq_dimensional
  refine ⟨hdeltaC, halpha, ?_⟩
  intro L m y n
  refine (Sreg.tail L _ hdeltaC halpha m y n).trans (ENNReal.ofReal_le_ofReal ?_)
  let rateM : ℝ := (1 - (1 - ((d : ℝ) - t) / 4)) ^ 2 /
    (Sreg.C * M.delta ^ 2 * |Real.log M.delta|)
  have hrr : rate ≤ rateM := hrateM.le
  have hmax : (n : ℝ) - Sreg.C ≤ max ((n : ℝ) - Sreg.C) 0 := le_max_left _ _
  have hnonneg : 0 ≤ max ((n : ℝ) - Sreg.C) 0 := le_max_right _ _
  have hprod := mul_le_mul_of_nonneg_right hrr hnonneg
  have hprod' := mul_le_mul_of_nonneg_left hmax hrate0
  have hexp : -(rateM * max ((n : ℝ) - Sreg.C) 0) ≤
      rate * Sreg.C + -rate * n := by linarith only [hprod, hprod']
  have hid : (1 - (1 - ((d : ℝ) - t) / 4)) ^ 2 *
      max ((n : ℝ) - Sreg.C) 0 / (Sreg.C * M.delta ^ 2 * |Real.log M.delta|) =
        rateM * max ((n : ℝ) - Sreg.C) 0 := by dsimp [rateM]; ring
  rw [hid]
  calc
    Sreg.C * Real.exp (-(rateM * max ((n : ℝ) - Sreg.C) 0)) ≤
        Sreg.C * Real.exp (rate * Sreg.C + -rate * n) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) Sreg.C_pos.le
    _ = A * Real.exp (-rate * n) := by rw [Real.exp_add, hCeq]; dsimp [A]; ring

/-- Regularity-prefix exponential moments are uniform over all sufficiently small-disorder models. -/
theorem prop_conc_uniform_prefix_moments
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (t q : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d)
    (ht0 : 0 < t) (hq : 1 ≤ q) :
    ∃ delta0 B : ℝ, 0 < delta0 ∧ 0 < B ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M),
        M.delta ≤ delta0 →
        M.delta ≤ Sreg.C⁻¹ ∧ 1 - ((d : ℝ) - t) / 4 ∈ Sreg.alphaRange ∧
        ∀ (L m : ℕ) (y : SpatialCoordinates d),
          eLpNorm (fun om => (3 : ℝ) ^ (t *
            (Sreg.prefixLen L (1 - ((d : ℝ) - t) / 4) m y om : ℝ)))
            (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B := by
  obtain ⟨delta0, A, rate, hdelta0, hA, hrate, htail⟩ :=
    aux_prop_conc_uniform_prefix_moments_tail d t q ht htd ht0 hq
  let lam : ℝ := q * t * Real.log 3
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hlam : 0 ≤ lam := mul_nonneg (mul_nonneg hq0.le ht0.le)
    (Real.log_nonneg (by norm_num))
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
  intro L m y
  let X := Sreg.prefixLen L (1 - ((d : ℝ) - t) / 4) m y
  have hmoment := aux_aux_macro_moment_bank_lintegral_exp_le
    (chaosSampleLaw M).toMeasure X (Sreg.prefix_measurable _ _ _ _)
    A rate lam hA hlam hrate (htM L m y)
  have hnorm := aux_aux_macro_moment_bank_eLpNorm_rpow_three_le
    (chaosSampleLaw M).toMeasure X t q hq0 V hmoment
  exact hnorm.trans_eq (ENNReal.ofReal_rpow_of_nonneg hV.le (by positivity))

end
end Paper
