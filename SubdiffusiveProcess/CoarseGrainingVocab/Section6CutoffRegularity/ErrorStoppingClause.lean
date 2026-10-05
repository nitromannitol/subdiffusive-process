module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.ErrorStoppingGeneric
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.WindowInputDischarge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.StoppingWitness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.ErrorStopping

@[expose] public section

/-!
# Conjunct (3) of `p.cutoff.regularity.good.scales`

The accumulated-error stopping clause
(`e.cutoff.regularity.error.stopping.tail` and
`e.cutoff.regularity.error.stopping`, `p.cutoff.regularity.good.scales` and `e.cutoff.regularity.error.stopping.tail` and `e.cutoff.regularity.error.stopping`), in the
exact frozen shape, assembled the same way as conjunct (4):

* the arbitrary-`s` depth tail of `ErrorStoppingGeneric.lean` (unshifted `q`),
* `exists_stopping_witness_ogammaLE_of_le` for the measurable witness, and
* the cutoff-generic pathwise bound
  `Section6Stopping.accumulatedError_sum_le_of_le_errorStoppingIndex`.

The frozen scale `C s^{-7} δ² |log δ| λ^{-2}` is exactly the reciprocal of
the rate produced by the tail, because the printed side condition
`λ ≥ C s^{-7/2} δ |log δ|^{1/2}` squares to it — the `s^{-7}` of the
conclusion is the square of the `s^{-7/2}` of the hypothesis.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open Homogenization hiding Vec
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

/-- `(s^{-7/2})² = s^{-7}`: the squaring that turns the printed hypothesis
exponent into the printed conclusion exponent. -/
theorem rpow_neg_seven_half_sq {s : ℝ} (hs : 0 < s) :
    (s ^ (-7 / 2 : ℝ)) ^ 2 = s ^ (-7 : ℤ) := by
  rw [← Real.rpow_natCast (s ^ (-7 / 2 : ℝ)) 2, ← Real.rpow_mul hs.le,
    show ((-7 / 2 : ℝ) * ((2 : ℕ) : ℝ)) = ((-7 : ℤ) : ℝ) by push_cast; ring,
    Real.rpow_intCast]

/-- Conjunct (3) of the frozen finite-cutoff good-scale proposition,
**unconditional**: the window-scale input it used to assume is discharged in
`WindowInputDischarge.lean`. -/
theorem exists_cutoff_regularity_error_stopping_clause
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, ∀ L : ℕ,
      ∀ s ∈ Set.Ioc 0 (1 / 2 : ℝ),
        C * M.delta ^ 2 * |Real.log M.delta| ≤ s →
        ∀ lambda ∈ Set.Ioc (0 : ℝ) 1,
          C * s ^ (-7 / 2 : ℝ) * M.delta *
              Real.sqrt |Real.log M.delta| ≤ lambda →
          ∀ m : ℕ, ∃ X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℤ,
            (∀ omega, X omega ∈ Set.Icc (-1 : ℤ) m) ∧
            SubdiffusiveProcess.OGammaLE M.P.toMeasure 1
              (C * s ^ (-7 : ℤ) * M.delta ^ 2 * |Real.log M.delta| *
                lambda⁻¹ ^ 2)
              (fun omega => max ((((m : ℤ) - X omega).toNat : ℝ) - 1) 0) ∧
            (∀ omega, 0 ≤ (m : ℤ) - X omega ∧
              ∀ n : ℕ, (n : ℤ) ≤ X omega →
                ∀ z : Vec d, OnTriadicGrid n z → z ∈ cube d m →
                  (∑ j ∈ Finset.Icc n m,
                    accumulatedError M (some L) j z s omega) ≤
                    lambda * ((m : ℝ) - (n : ℝ))) := by
  obtain ⟨K1, C1, hK1, hC1, htail⟩ :=
    exists_cutoffParameterizedErrorStoppingDepth_tail (d := d)
      (cutoffParameterizedErrorWindowInput_holds d)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨K1 + C1 + 4 * (1 + Real.log 2) * C1 ^ 2, by positivity, ?_⟩
  set C : ℝ := K1 + C1 + 4 * (1 + Real.log 2) * C1 ^ 2 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  intro M L s hs hsdelta lambda hlambda hlam m
  obtain ⟨hs0, hs2⟩ := hs
  obtain ⟨hl0, _hl1⟩ := hlambda
  have hs1 : s ≤ 1 := hs2.trans (by norm_num)
  have hd0 : 0 < M.delta := M.shellPrefix.delta_pos
  have hlogNeg : Real.log M.delta < 0 :=
    Real.log_neg hd0 (M.shellPrefix.delta_le_half.trans_lt (by norm_num))
  have hlogpos : 0 < |Real.log M.delta| := abs_pos.mpr hlogNeg.ne
  have hroot : 0 < Real.sqrt |Real.log M.delta| := Real.sqrt_pos.mpr hlogpos
  have hbase : (0 : ℝ) < M.delta ^ 2 * |Real.log M.delta| := by positivity
  -- the two constant comparisons
  have hK1C : K1 ≤ C := by rw [hCdef]; nlinarith [hC1.le, hlog2.le, sq_nonneg C1]
  have hC1C : C1 ≤ C := by rw [hCdef]; nlinarith [hK1.le, hlog2.le, sq_nonneg C1]
  have hsqC : 4 * (1 + Real.log 2) * C1 ^ 2 ≤ C := by
    rw [hCdef]; linarith [hK1.le, hC1.le]
  -- the budget hypothesis
  have hbudget : K1 * M.delta ^ 2 * |Real.log M.delta| ≤ s := by
    refine le_trans ?_ hsdelta
    calc K1 * M.delta ^ 2 * |Real.log M.delta|
        = K1 * (M.delta ^ 2 * |Real.log M.delta|) := by ring
      _ ≤ C * (M.delta ^ 2 * |Real.log M.delta|) :=
          mul_le_mul_of_nonneg_right hK1C hbase.le
      _ = C * M.delta ^ 2 * |Real.log M.delta| := by ring
  -- the threshold hypothesis
  set P : ℝ := s ^ (-7 / 2 : ℝ) * M.delta * Real.sqrt |Real.log M.delta|
    with hPdef
  have hPpos : 0 < P := by
    rw [hPdef]
    exact mul_pos (mul_pos (Real.rpow_pos_of_pos hs0 _) hd0) hroot
  have hlamC1 : C1 * s ^ (-7 / 2 : ℝ) * M.delta *
      Real.sqrt |Real.log M.delta| ≤ lambda := by
    refine le_trans ?_ hlam
    have hmono : C1 * P ≤ C * P := mul_le_mul_of_nonneg_right hC1C hPpos.le
    calc C1 * s ^ (-7 / 2 : ℝ) * M.delta * Real.sqrt |Real.log M.delta|
        = C1 * P := by rw [hPdef]; ring
      _ ≤ C * P := hmono
      _ = C * s ^ (-7 / 2 : ℝ) * M.delta * Real.sqrt |Real.log M.delta| := by
          rw [hPdef]; ring
  -- the rate produced by the arbitrary-`s` tail
  set r : ℝ := lambda ^ 2 / (C1 * s ^ (-7 / 2 : ℝ) * M.delta *
    Real.sqrt |Real.log M.delta|) ^ 2 with hrdef
  have hC1P : C1 * s ^ (-7 / 2 : ℝ) * M.delta *
      Real.sqrt |Real.log M.delta| = C1 * P := by rw [hPdef]; ring
  have hrpos : 0 < r := by
    rw [hrdef, hC1P]
    exact div_pos (pow_pos hl0 2) (pow_pos (mul_pos hC1 hPpos) 2)
  set Jstop : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℤ :=
    fun omega => (errorStoppingIndex M (some L) lambda s m omega : ℤ)
    with hJstopdef
  have hJ : ∀ omega, Jstop omega ∈ Set.Icc (-1 : ℤ) (m : ℤ) := fun omega =>
    (errorStoppingIndex M (some L) lambda s m omega).property
  have htail' : ∀ q : ℕ, 0 < q →
      M.P.toMeasure.real {omega | q < ((m : ℤ) - Jstop omega).toNat} ≤
        2 * Real.exp (-(r * (q : ℝ))) := by
    intro q hq
    have hset : {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d |
          q < ((m : ℤ) - Jstop omega).toNat} =
        {omega | q < cutoffErrorStoppingDepth M L lambda s m omega} := rfl
    rw [hset]
    have h := htail M s hs0 hs1 hbudget lambda hlamC1 L q m hq
    refine h.trans (le_of_eq ?_)
    rw [hrdef]
  -- the frozen scale dominates the sharp scale
  have hscale : depthGammaOneScaleSharp 2 r ≤
      C * s ^ (-7 : ℤ) * M.delta ^ 2 * |Real.log M.delta| * lambda⁻¹ ^ 2 := by
    have hPsq : P ^ 2 = s ^ (-7 : ℤ) * M.delta ^ 2 * |Real.log M.delta| := by
      rw [hPdef, mul_pow, mul_pow, rpow_neg_seven_half_sq hs0,
        Real.sq_sqrt hlogpos.le]
    have hsharp : depthGammaOneScaleSharp 2 r =
        4 * (1 + Real.log 2) * C1 ^ 2 * P ^ 2 * lambda⁻¹ ^ 2 := by
      rw [depthGammaOneScaleSharp, depthTailScaleSharp, hrdef, hC1P]
      rw [div_div_eq_mul_div, mul_comm]
      field_simp [hl0.ne', hC1.ne', hPpos.ne']
    rw [hsharp]
    have hlinv : (0 : ℝ) < lambda⁻¹ ^ 2 := by positivity
    have hstep : 4 * (1 + Real.log 2) * C1 ^ 2 * P ^ 2 ≤
        C * P ^ 2 := mul_le_mul_of_nonneg_right hsqC (sq_nonneg P)
    calc 4 * (1 + Real.log 2) * C1 ^ 2 * P ^ 2 * lambda⁻¹ ^ 2
        ≤ C * P ^ 2 * lambda⁻¹ ^ 2 :=
          mul_le_mul_of_nonneg_right hstep hlinv.le
      _ = C * s ^ (-7 : ℤ) * M.delta ^ 2 * |Real.log M.delta| *
            lambda⁻¹ ^ 2 := by rw [hPsq]; ring
  obtain ⟨X, hrange, hdom, hog⟩ :=
    exists_stopping_witness_ogammaLE_of_le (μ := M.P.toMeasure) m Jstop hJ
      (by norm_num : (1 : ℝ) ≤ 2) hrpos hscale htail'
  refine ⟨X, hrange, hog, ?_⟩
  intro omega
  refine ⟨by have := (hrange omega).2; omega, ?_⟩
  intro n hn z hzgrid hzmem
  exact accumulatedError_sum_le_of_le_errorStoppingIndex
    M (some L) lambda s m n omega (hn.trans (hdom omega)) z hzgrid hzmem

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
