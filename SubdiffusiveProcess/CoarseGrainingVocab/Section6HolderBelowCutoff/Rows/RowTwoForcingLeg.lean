import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.RowTwoRatioScales
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoRatioScales
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.GateParameters
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.GateParameters
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder.StoppedRatio

/-!
# Row 2's forcing leg

The second leg of the split Step-6 budget is

```text
  s^{-6} * sigma^{-1/2} * 3^{s * gate} * [g]_{H^s(U_{m,gate}(x))} ,
```

and the frozen row-2 datum term is
`b^{-1/2} * 3^{m/2} * [g]_{W^{1/2,∞}(cu_m)}`.  Three landed facts turn the first
into the second:

* `Section6Holder.forcing_fractional_window_le` — the Besov/Hölder embedding at
  a truncated window, whose `3^{s j}` and `3^{j(1/2-s)}` combine to `3^{j/2}`;
* `3^{gate/2} ≤ 3^{m/2}`, the window sitting inside the domain;
* `sigma^{-1/2} ≤ exp(C lambda (m-n)) b^{-1/2}`, the *second* direction of
  `stopped_tailAverage_ratio_bounds_exp_cut`, paired against `b/b`.

No dimension enters beyond `fractionalHolderConst d`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows

open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- The dimension-only constant of row 2's forcing leg. -/
def rowTwoForcingConst_cut (d : ℕ) : ℝ :=
  (interiorFractionalOrder_cut).1 ^ (-6 : ℝ) *
    Section6ExcessDecay.fractionalHolderConst d *
    Real.sqrt (interiorFractionalOrder_cut).1

theorem rowTwoForcingConst_nonneg_cut (d : ℕ) : 0 ≤ rowTwoForcingConst_cut d := by
  rw [rowTwoForcingConst_cut, interiorFractionalOrder_val]
  have := Section6ExcessDecay.fractionalHolderConst_nonneg d
  positivity

/-- The reciprocal square root of the local coefficient average against the
domain-scale one. -/
theorem inv_sqrt_tailAverage_le_cut (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (C1 C2 alpha : ℝ) (step m n q L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d)
    (hzgrid : OnTriadicGrid n z) (hz : z ∈ cube d m)
    (hstop : (Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
        (Section6Stopping.holderStoppingLambda C1 alpha)
        (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
      (m : ℤ) - (n : ℤ))
    (hnm : n < m) (hnq : n ≤ q) (hqm : q ≤ m)     (hlambda0 : 0 ≤ Section6Stopping.holderStoppingLambda C1 alpha)
    (hlambda1 : Section6Stopping.holderStoppingLambda C1 alpha < 1)
    (hepsilon : 0 ≤ Section6Stopping.holderStoppingEpsilon C2 alpha)
    (hdelta : M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha) :
    (Real.sqrt (tailAverage M L q omega (translatedCube d (q : ℕ) z)))⁻¹ ≤
      rowTwoRatioBound_cut d C1 alpha m n *
        (Real.sqrt (tailCoefficientCubeAverage M L m omega))⁻¹ := by
  have hb : 0 < tailCoefficientCubeAverage M L m omega :=
    tailCoefficientCubeAverage_pos M L m omega
  have hsig : 0 < tailAverage M L q omega (translatedCube d (q : ℕ) z) :=
    tailAverage_translatedCube_pos_cut M L q omega z
  have hE1 : (1 : ℝ) ≤ rowTwoRatioBound_cut d C1 alpha m n :=
    one_le_rowTwoRatioBound_cut d hlambda0 (le_of_lt hnm)
  have hbounds := stoppedRatio_bounds_at_cut M C1 C2 alpha step m n q L omega z
    hzgrid hz hstop hnm hnq hqm hlambda0 hlambda1 hepsilon hdelta
  have hpair := sqrt_tailAverage_pairing (sigmaN := tailCoefficientCubeAverage M L m omega)
    (sigmaTop := tailAverage M L q omega (translatedCube d (q : ℕ) z))
    (b := tailCoefficientCubeAverage M L m omega)
    (E := rowTwoRatioBound_cut d C1 alpha m n) hb.le hsig hb
    (rowTwoRatioBound_nonneg_cut d C1 alpha m n)
    (by rw [div_self hb.ne']; exact hE1) hbounds.2
  have hrootb : 0 < Real.sqrt (tailCoefficientCubeAverage M L m omega) :=
    Real.sqrt_pos.2 hb
  have hsplit : (Real.sqrt (tailAverage M L q omega
        (translatedCube d (q : ℕ) z)))⁻¹ =
      (Real.sqrt (tailCoefficientCubeAverage M L m omega) *
        (Real.sqrt (tailAverage M L q omega (translatedCube d (q : ℕ) z)))⁻¹) *
        (Real.sqrt (tailCoefficientCubeAverage M L m omega))⁻¹ := by
    field_simp
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hpair (inv_nonneg.mpr hrootb.le)

/-- **Row 2's forcing leg.** -/
theorem interiorRowTwo_forcingLeg_cut [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (C1 C2 alpha : ℝ)
    (step m n gate L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z x : Vec d)
    (hzgrid : OnTriadicGrid n z) (hz : z ∈ cube d m) (hx : x ∈ cube d (m : ℤ))
    (hstop : (Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
        (Section6Stopping.holderStoppingLambda C1 alpha)
        (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
      (m : ℤ) - (n : ℤ))
    (hnm : n < m) (hng : n ≤ gate + 2) (hgm : gate + 2 ≤ m)     (hlambda0 : 0 ≤ Section6Stopping.holderStoppingLambda C1 alpha)
    (hlambda1 : Section6Stopping.holderStoppingLambda C1 alpha < 1)
    (hepsilon : 0 ≤ Section6Stopping.holderStoppingEpsilon C2 alpha)
    (hdelta : M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha)
    (g : Vec d → Vec d) (hg : MemHolder (cube d (m : ℤ)) (1 / 2) g) :
    (interiorFractionalOrder_cut).1 ^ (-6 : ℝ) *
        (Real.sqrt (tailAverage M L (gate + 2) omega
          (translatedCube d ((gate : ℤ) + 2) z)))⁻¹ *
        (3 : ℝ) ^ ((interiorFractionalOrder_cut).1 * (gate : ℝ)) *
        (fractionalSeminormOn (truncatedCube d (m : ℤ) (gate : ℤ) x)
          (interiorFractionalOrder_cut).1 g).toReal ≤
      rowTwoForcingConst_cut d * rowTwoRatioBound_cut d C1 alpha m n *
        ((tailAverage M L m omega (cube d (m : ℤ))) ^ (-1 / 2 : ℝ) *
          (3 : ℝ) ^ ((m : ℝ) / 2) *
          holderSeminormOn (cube d (m : ℤ)) (1 / 2) g) := by
  have hb : 0 < tailCoefficientCubeAverage M L m omega :=
    tailCoefficientCubeAverage_pos M L m omega
  have hbeq : tailCoefficientCubeAverage M L m omega =
      tailAverage M L m omega (cube d (m : ℤ)) :=
    tailCoefficientCubeAverage_eq_tailAverage_cube M L m omega
  have hb12 : (tailAverage M L m omega (cube d (m : ℤ))) ^ (-1 / 2 : ℝ) =
      (Real.sqrt (tailCoefficientCubeAverage M L m omega))⁻¹ := by
    rw [hbeq, show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
      Real.rpow_neg (by rw [← hbeq]; exact hb.le), ← Real.sqrt_eq_rpow]
  -- the coefficient factor
  have hcast : ((gate + 2 : ℕ) : ℤ) = (gate : ℤ) + 2 := by push_cast; ring
  have hinv := inv_sqrt_tailAverage_le_cut M C1 C2 alpha step m n (gate + 2) L omega z
    hzgrid hz hstop hnm hng hgm hlambda0 hlambda1 hepsilon hdelta
  rw [hcast] at hinv
  -- the embedding
  have hembed := Section6Holder.forcing_fractional_window_le (d := d)
    (m := (m : ℤ)) (j := (gate : ℤ)) (x := x) (g := g)
    (s := (interiorFractionalOrder_cut).1) hx
    (by rw [interiorFractionalOrder_val]; norm_num)
    (by rw [interiorFractionalOrder_val]) hg
  -- the window power against the domain power
  have hpow : (3 : ℝ) ^ (((gate : ℤ) : ℝ) / 2) ≤ (3 : ℝ) ^ ((m : ℝ) / 2) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have : ((gate : ℤ) : ℝ) ≤ (m : ℝ) := by
      have : (gate : ℤ) ≤ (m : ℤ) := by omega
      exact_mod_cast this
    linarith
  set F : ℝ := (fractionalSeminormOn (truncatedCube d (m : ℤ) (gate : ℤ) x)
    (interiorFractionalOrder_cut).1 g).toReal with hFdef
  set S : ℝ := (Real.sqrt (tailAverage M L (gate + 2) omega
    (translatedCube d ((gate : ℤ) + 2) z)))⁻¹ with hSdef
  set E : ℝ := rowTwoRatioBound_cut d C1 alpha m n with hEdef
  set H : ℝ := holderSeminormOn (cube d (m : ℤ)) (1 / 2) g with hHdef
  set B : ℝ := (Real.sqrt (tailCoefficientCubeAverage M L m omega))⁻¹ with hBdef
  have hH0 : 0 ≤ H := Section6ExcessDecay.holderSeminormOn_nonneg hg
  have hB0 : 0 ≤ B := by
    rw [hBdef]; exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hS0 : 0 ≤ S := by rw [hSdef]; exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hs6 : (0 : ℝ) ≤ (interiorFractionalOrder_cut).1 ^ (-6 : ℝ) := by
    rw [interiorFractionalOrder_val]; positivity
  have hgateR : ((gate : ℤ) : ℝ) = (gate : ℝ) := by push_cast; ring
  rw [hgateR] at hembed hpow
  -- assemble
  have hkey : (3 : ℝ) ^ ((interiorFractionalOrder_cut).1 * (gate : ℝ)) * F ≤
      Section6ExcessDecay.fractionalHolderConst d *
        Real.sqrt (interiorFractionalOrder_cut).1 * (3 : ℝ) ^ ((m : ℝ) / 2) * H := by
    refine hembed.trans ?_
    have hc0 : (0 : ℝ) ≤ Section6ExcessDecay.fractionalHolderConst d *
        Real.sqrt (interiorFractionalOrder_cut).1 :=
      mul_nonneg (Section6ExcessDecay.fractionalHolderConst_nonneg d)
        (Real.sqrt_nonneg _)
    have := mul_le_mul_of_nonneg_left hpow hc0
    calc Section6ExcessDecay.fractionalHolderConst d *
          Real.sqrt (interiorFractionalOrder_cut).1 * (3 : ℝ) ^ ((gate : ℝ) / 2) * H
        ≤ Section6ExcessDecay.fractionalHolderConst d *
            Real.sqrt (interiorFractionalOrder_cut).1 * (3 : ℝ) ^ ((m : ℝ) / 2) * H := by
          exact mul_le_mul_of_nonneg_right this hH0
      _ = _ := by ring
  have hkey0 : (0 : ℝ) ≤ (3 : ℝ) ^ ((interiorFractionalOrder_cut).1 * (gate : ℝ)) * F := by
    have hF0 : 0 ≤ F := ENNReal.toReal_nonneg
    positivity
  rw [hb12]
  calc (interiorFractionalOrder_cut).1 ^ (-6 : ℝ) * S *
        (3 : ℝ) ^ ((interiorFractionalOrder_cut).1 * (gate : ℝ)) * F
      = ((interiorFractionalOrder_cut).1 ^ (-6 : ℝ)) * (S *
          ((3 : ℝ) ^ ((interiorFractionalOrder_cut).1 * (gate : ℝ)) * F)) := by ring
    _ ≤ ((interiorFractionalOrder_cut).1 ^ (-6 : ℝ)) * ((E * B) *
          (Section6ExcessDecay.fractionalHolderConst d *
            Real.sqrt (interiorFractionalOrder_cut).1 *
            (3 : ℝ) ^ ((m : ℝ) / 2) * H)) := by
        refine mul_le_mul_of_nonneg_left ?_ hs6
        refine mul_le_mul hinv hkey hkey0 ?_
        exact mul_nonneg (rowTwoRatioBound_nonneg_cut d C1 alpha m n) hB0
    _ = rowTwoForcingConst_cut d * E * (B * (3 : ℝ) ^ ((m : ℝ) / 2) * H) := by
        rw [rowTwoForcingConst_cut]; ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows
