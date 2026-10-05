module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.HolderScale

@[expose] public section

/-!
# The finite-cutoff stopping scale for the Holder iteration

This file specializes the general stopping indices to `some L`.  It
provides the deterministic and measurable carriers needed by the
cutoff-uniform Holder argument, independently of the analytic estimates used
to bound their tails.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping

open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- Natural-valued readout of the combined stopping depth at cutoff `L`. -/
def cutoffHolderStoppingScale {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (alpha lambda epsilon : ℝ) (step m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℕ :=
  Int.toNat
    (regularityMinimalScale M (some L) alpha lambda epsilon holderStoppingS
      step m omega)

theorem cutoffRegularityMinimalScale_nonneg {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (alpha lambda epsilon s : ℝ) (step m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ regularityMinimalScale M (some L) alpha lambda epsilon s step m omega := by
  have herr := (errorStoppingIndex M (some L) lambda s m omega).property.2
  have hgood :=
    (goodStoppingIndex M (some L) lambda epsilon s m omega).property.2
  unfold regularityMinimalScale
  omega

theorem cutoffHolderStoppingScale_intCast {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (alpha lambda epsilon : ℝ) (step m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    (cutoffHolderStoppingScale M L alpha lambda epsilon step m omega : ℤ) =
      regularityMinimalScale M (some L) alpha lambda epsilon holderStoppingS
        step m omega := by
  unfold cutoffHolderStoppingScale
  exact Int.toNat_of_nonneg
    (cutoffRegularityMinimalScale_nonneg M L alpha lambda epsilon
      holderStoppingS step m omega)

theorem cutoffHolderStoppingScale_pos {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (alpha lambda epsilon : ℝ) (step m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 < cutoffHolderStoppingScale M L alpha lambda epsilon step m omega := by
  have hreg : (5 : ℤ) ≤
      regularityMinimalScale M (some L) alpha lambda epsilon holderStoppingS
        step m omega := by
    have herr :=
      (errorStoppingIndex M (some L) lambda holderStoppingS m omega).property.2
    have hgood :=
      (goodStoppingIndex M (some L) lambda epsilon holderStoppingS m omega).property.2
    unfold regularityMinimalScale
    omega
  rw [← cutoffHolderStoppingScale_intCast M L alpha lambda epsilon step m omega]
    at hreg
  omega

/-- Depth of the cutoff accumulated-error stopping index. -/
def cutoffErrorStoppingDepth {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (lambda s : ℝ) (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℕ :=
  Int.toNat ((m : ℤ) - (errorStoppingIndex M (some L) lambda s m omega : ℤ))

/-- Depth of the cutoff good-density stopping index. -/
def cutoffGoodStoppingDepth {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (lambda epsilon s : ℝ) (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℕ :=
  Int.toNat
    ((m : ℤ) - (goodStoppingIndex M (some L) lambda epsilon s m omega : ℤ))

theorem cutoffHolderStoppingScale_eq_max_depth_add {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (alpha lambda epsilon : ℝ) (step m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    cutoffHolderStoppingScale M L alpha lambda epsilon step m omega =
      max (cutoffErrorStoppingDepth M L lambda holderStoppingS m omega)
          (cutoffGoodStoppingDepth M L lambda epsilon holderStoppingS m omega) +
        step + 5 := by
  have herrUpper :=
    (errorStoppingIndex M (some L) lambda holderStoppingS m omega).property.2
  have hgoodUpper :=
    (goodStoppingIndex M (some L) lambda epsilon holderStoppingS m omega).property.2
  have herrNonneg : 0 ≤
      (m : ℤ) - (errorStoppingIndex M (some L) lambda holderStoppingS m omega : ℤ) :=
    by omega
  have hgoodNonneg : 0 ≤
      (m : ℤ) -
        (goodStoppingIndex M (some L) lambda epsilon holderStoppingS m omega : ℤ) :=
    by omega
  apply Int.ofNat_injective
  change (cutoffHolderStoppingScale M L alpha lambda epsilon step m omega : ℤ) =
    (max (cutoffErrorStoppingDepth M L lambda holderStoppingS m omega)
      (cutoffGoodStoppingDepth M L lambda epsilon holderStoppingS m omega) +
        step + 5 : ℕ)
  rw [cutoffHolderStoppingScale_intCast]
  unfold regularityMinimalScale cutoffErrorStoppingDepth cutoffGoodStoppingDepth
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_ofNat, Nat.cast_max,
    Int.toNat_of_nonneg herrNonneg, Int.toNat_of_nonneg hgoodNonneg]

/-- Removing the deterministic safety margin from a large combined depth
leaves a large error depth or a large good-density depth. -/
theorem cutoffHolderStoppingScale_tail_subset {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (alpha lambda epsilon : ℝ) (step m k : ℕ) (hk : step + 5 ≤ k) :
    {omega | k < cutoffHolderStoppingScale M L alpha lambda epsilon step m omega} ⊆
      {omega | k - (step + 5) <
        cutoffErrorStoppingDepth M L lambda holderStoppingS m omega} ∪
      {omega | k - (step + 5) <
        cutoffGoodStoppingDepth M L lambda epsilon holderStoppingS m omega} := by
  intro omega homega
  change k < cutoffHolderStoppingScale M L alpha lambda epsilon step m omega at homega
  rw [cutoffHolderStoppingScale_eq_max_depth_add] at homega
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  omega

theorem cutoffHolderStoppingScale_le_add {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (alpha lambda epsilon : ℝ) (step m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    cutoffHolderStoppingScale M L alpha lambda epsilon step m omega ≤
      m + step + 6 := by
  have herr :=
    (errorStoppingIndex M (some L) lambda holderStoppingS m omega).property
  have hgood :=
    (goodStoppingIndex M (some L) lambda epsilon holderStoppingS m omega).property
  have herrLower : (-1 : ℤ) ≤
      (errorStoppingIndex M (some L) lambda holderStoppingS m omega : ℤ) := herr.1
  have hgoodLower : (-1 : ℤ) ≤
      (goodStoppingIndex M (some L) lambda epsilon holderStoppingS m omega : ℤ) :=
    hgood.1
  have hmax : max
      ((m : ℤ) - (errorStoppingIndex M (some L) lambda holderStoppingS m omega : ℤ))
      ((m : ℤ) -
        (goodStoppingIndex M (some L) lambda epsilon holderStoppingS m omega : ℤ)) ≤
      (m : ℤ) + 1 := by
    rw [max_le_iff]
    constructor <;> omega
  have hreg :
      regularityMinimalScale M (some L) alpha lambda epsilon holderStoppingS
          step m omega ≤ ((m + step + 6 : ℕ) : ℤ) := by
    unfold regularityMinimalScale
    calc
      max
          ((m : ℤ) -
            (errorStoppingIndex M (some L) lambda holderStoppingS m omega : ℤ))
          ((m : ℤ) -
            (goodStoppingIndex M (some L) lambda epsilon holderStoppingS m omega : ℤ)) +
          (step : ℤ) + 5 ≤ ((m : ℤ) + 1) + (step : ℤ) + 5 := by omega
      _ = ((m + step + 6 : ℕ) : ℤ) := by push_cast; ring
  rw [← cutoffHolderStoppingScale_intCast M L alpha lambda epsilon step m omega]
    at hreg
  exact_mod_cast hreg

/-- Measurable hull of the literal cutoff stopping scale. -/
def measurableCutoffHolderStoppingScale {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (alpha lambda epsilon : ℝ) (step m : ℕ) : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ :=
  measurableNatEnvelope M.P.toMeasure
    (cutoffHolderStoppingScale M L alpha lambda epsilon step m) (m + step + 6)

theorem measurable_measurableCutoffHolderStoppingScale {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (alpha lambda epsilon : ℝ) (step m : ℕ) :
    Measurable (measurableCutoffHolderStoppingScale M L alpha lambda epsilon step m) :=
  measurable_measurableNatEnvelope _ _ _

theorem cutoffHolderStoppingScale_le_measurable {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (alpha lambda epsilon : ℝ) (step m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    cutoffHolderStoppingScale M L alpha lambda epsilon step m omega ≤
      measurableCutoffHolderStoppingScale M L alpha lambda epsilon step m omega :=
  le_measurableNatEnvelope
    (cutoffHolderStoppingScale_le_add M L alpha lambda epsilon step m omega)

theorem measurableCutoffHolderStoppingScale_pos {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (alpha lambda epsilon : ℝ) (step m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 < measurableCutoffHolderStoppingScale M L alpha lambda epsilon step m omega :=
  (cutoffHolderStoppingScale_pos M L alpha lambda epsilon step m omega).trans_le
    (cutoffHolderStoppingScale_le_measurable M L alpha lambda epsilon step m omega)

theorem measure_measurableCutoffHolderStoppingScale_tail_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (alpha lambda epsilon : ℝ) (step m k : ℕ) :
    M.P.toMeasure {omega |
        k < measurableCutoffHolderStoppingScale M L alpha lambda epsilon step m omega} ≤
      M.P.toMeasure {omega |
        k < cutoffHolderStoppingScale M L alpha lambda epsilon step m omega} :=
  measure_measurableNatEnvelope_tail_le _ _ _ _

theorem measure_measurableCutoffHolderStoppingScale_tail_le_add {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (alpha lambda epsilon : ℝ) (step m k : ℕ) (hk : step + 5 ≤ k) :
    M.P.toMeasure {omega |
        k < measurableCutoffHolderStoppingScale M L alpha lambda epsilon step m omega} ≤
      M.P.toMeasure {omega | k - (step + 5) <
          cutoffErrorStoppingDepth M L lambda holderStoppingS m omega} +
        M.P.toMeasure {omega | k - (step + 5) <
          cutoffGoodStoppingDepth M L lambda epsilon holderStoppingS m omega} := by
  calc
    M.P.toMeasure {omega |
        k < measurableCutoffHolderStoppingScale M L alpha lambda epsilon step m omega} ≤
      M.P.toMeasure {omega |
        k < cutoffHolderStoppingScale M L alpha lambda epsilon step m omega} :=
      measure_measurableCutoffHolderStoppingScale_tail_le
        M L alpha lambda epsilon step m k
    _ ≤ M.P.toMeasure
          ({omega | k - (step + 5) <
              cutoffErrorStoppingDepth M L lambda holderStoppingS m omega} ∪
            {omega | k - (step + 5) <
              cutoffGoodStoppingDepth M L lambda epsilon holderStoppingS m omega}) :=
      MeasureTheory.measure_mono
        (cutoffHolderStoppingScale_tail_subset
          M L alpha lambda epsilon step m k hk)
    _ ≤ M.P.toMeasure {omega | k - (step + 5) <
          cutoffErrorStoppingDepth M L lambda holderStoppingS m omega} +
        M.P.toMeasure {omega | k - (step + 5) <
          cutoffGoodStoppingDepth M L lambda epsilon holderStoppingS m omega} :=
      MeasureTheory.measure_union_le _ _

theorem le_cutoffStoppingIndices_of_stoppingScale_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (alpha lambda epsilon : ℝ) (step m n : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hn : (cutoffHolderStoppingScale M L alpha lambda epsilon step m omega : ℤ) ≤
      (m : ℤ) - (n : ℤ)) :
    (n : ℤ) ≤ errorStoppingIndex M (some L) lambda holderStoppingS m omega ∧
      (n : ℤ) ≤
        goodStoppingIndex M (some L) lambda epsilon holderStoppingS m omega := by
  rw [cutoffHolderStoppingScale_intCast] at hn
  unfold regularityMinimalScale at hn
  constructor <;> omega

/-- Both cutoff stopping conclusions after the combined stopping depth. -/
theorem cutoffHolder_stopped_controls {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (alpha lambda epsilon : ℝ) (step m n : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hn : (cutoffHolderStoppingScale M L alpha lambda epsilon step m omega : ℤ) ≤
      (m : ℤ) - (n : ℤ))
    (z : Vec d) (hzgrid : OnTriadicGrid n z) (hzmem : z ∈ cube d m) :
    (∑ j ∈ Finset.Icc n m, accumulatedError M (some L) j z holderStoppingS omega) ≤
        lambda * ((m : ℝ) - (n : ℝ)) ∧
      (∑ j ∈ Finset.Icc n m,
          (1 - if omega ∈ goodEvent M (some L) j z epsilon holderStoppingS then
            1 else 0)) <
        1 + lambda * ((m : ℝ) - (n : ℝ)) := by
  obtain ⟨herr, hgood⟩ :=
    le_cutoffStoppingIndices_of_stoppingScale_le
      M L alpha lambda epsilon step m n omega hn
  exact ⟨
    accumulatedError_sum_le_of_le_errorStoppingIndex
      M (some L) lambda holderStoppingS m n omega herr z hzgrid hzmem,
    badScaleCount_lt_of_le_goodStoppingIndex
      M (some L) lambda epsilon holderStoppingS m n omega hgood z hzgrid hzmem⟩

theorem measurableCutoffHolder_stopped_controls_at_parameters {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (C1 C2 alpha : ℝ) (step m n : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hn : (measurableCutoffHolderStoppingScale M L alpha
        (holderStoppingLambda C1 alpha) (holderStoppingEpsilon C2 alpha)
        step m omega : ℤ) ≤ (m : ℤ) - (n : ℤ))
    (z : Vec d) (hzgrid : OnTriadicGrid n z) (hzmem : z ∈ cube d m) :
    (∑ j ∈ Finset.Icc n m,
        accumulatedError M (some L) j z holderStoppingS omega) ≤
        holderStoppingLambda C1 alpha * ((m : ℝ) - (n : ℝ)) ∧
      (∑ j ∈ Finset.Icc n m,
          (1 - if omega ∈ goodEvent M (some L) j z
            (holderStoppingEpsilon C2 alpha) holderStoppingS then 1 else 0)) <
        1 + holderStoppingLambda C1 alpha * ((m : ℝ) - (n : ℝ)) := by
  have hle := cutoffHolderStoppingScale_le_measurable M L alpha
    (holderStoppingLambda C1 alpha) (holderStoppingEpsilon C2 alpha) step m omega
  have hraw :
      (cutoffHolderStoppingScale M L alpha (holderStoppingLambda C1 alpha)
        (holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
          (m : ℤ) - (n : ℤ) := (Int.ofNat_le.2 hle).trans hn
  exact cutoffHolder_stopped_controls M L alpha (holderStoppingLambda C1 alpha)
    (holderStoppingEpsilon C2 alpha) step m n omega hraw z hzgrid hzmem

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
