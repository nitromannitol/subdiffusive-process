module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.DualAnnealedMonotone
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepFiniteReadoutComparison

@[expose] public section

/-!
# Step 3: the annealed response is dominated by the coarse contrast

With the dual monotonicity of `DualAnnealedMonotone.lean` in hand, the
comparison the §44 programme needs becomes elementary.

Writing `alpha = ahom M L`, `A = abarScalarReadout M L j` and
`B = oneStepAnnealedDualReadout M L j`, `expectedJ_eq_scalar_readouts` gives

    `E[J] = ½ alpha⁻¹ A + ½ alpha B - 1 = ½ u + ½ v - 1`,
    `u := alpha⁻¹ A`,  `v := alpha B`,

and the **coarse contrast** is `A * B = u * v`.  Both `u ≥ 1` and
`v ≥ 1` are now available:

* `u ≥ 1` from `ahom ≤ abarScalarReadout` (the primal readout is antitone with
  limit `ahom`);
* `v ≥ 1` from `ahom_inv_le_oneStepAnnealedDualReadout` (this bundle's dual).

Since `u, v ≥ 1` force `2 u v ≥ u + v`, we get `E[J] ≤ A * B - 1`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-- `ahom` is a lower bound for every centered-cube primal readout. -/
theorem ahom_le_abarScalarReadout
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L j : ℕ) :
    ahom M L ≤ abarScalarReadout M L j := by
  refine le_of_tendsto (tendsto_abarScalarReadout_ahom M L) ?_
  filter_upwards [Filter.eventually_ge_atTop j] with k hk
  exact antitone_abarScalarReadout M L hk

/-- **Step 3.**  The annealed normalized response on the centered scale-`j` cube
is dominated by the coarse contrast minus one. -/
theorem expectedJ_le_coarseContrast_sub_one [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L j : ℕ)
    (e : Vec d) (he : vecNormSq e = 1) :
    expectedJ M L j ((Real.sqrt (ahom M L))⁻¹ • e)
        (Real.sqrt (ahom M L) • e) ≤
      abarScalarReadout M L j * oneStepAnnealedDualReadout M L j - 1 := by
  have halpha : 0 < ahom M L :=
    (Real.exp_pos _).trans_le
      (SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M L)
  set A : ℝ := abarScalarReadout M L j with hA
  set B : ℝ := oneStepAnnealedDualReadout M L j with hB
  have hu : 1 ≤ (ahom M L)⁻¹ * A := by
    rw [← inv_mul_cancel₀ halpha.ne']
    exact mul_le_mul_of_nonneg_left (ahom_le_abarScalarReadout M L j)
      (inv_nonneg.mpr halpha.le)
  have hv : 1 ≤ ahom M L * B := by
    rw [← mul_inv_cancel₀ halpha.ne']
    exact mul_le_mul_of_nonneg_left
      (ahom_inv_le_oneStepAnnealedDualReadout M L j) halpha.le
  have hprod : ((ahom M L)⁻¹ * A) * (ahom M L * B) = A * B := by
    field_simp
  rw [expectedJ_eq_scalar_readouts M L j e he]
  have hkey : (1 / 2 : ℝ) * ((ahom M L)⁻¹ * A) +
      (1 / 2 : ℝ) * (ahom M L * B) ≤ ((ahom M L)⁻¹ * A) * (ahom M L * B) := by
    nlinarith [hu, hv]
  rw [hprod] at hkey
  have hrw : (1 / 2 : ℝ) * (ahom M L)⁻¹ * A +
      (1 / 2 : ℝ) * ahom M L * B - 1 =
      ((1 / 2 : ℝ) * ((ahom M L)⁻¹ * A) +
        (1 / 2 : ℝ) * (ahom M L * B)) - 1 := by ring
  rw [hrw]
  linarith [hkey]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
