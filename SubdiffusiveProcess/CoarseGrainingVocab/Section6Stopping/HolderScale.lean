module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.ErrorStopping
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.GoodStopping
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.MeasurableNatEnvelope
public import SubdiffusiveProcess.Frozen.Section6.Defs.RegularityMinimalScale

@[expose] public section

/-!
# The stopping scale used by the Hölder argument

The Hölder proof uses the fixed exponent `s₀ = 1 / 32` and no response
cutoff.  This file packages the two frozen first-failure indices into a
natural-valued depth and proves the two pathwise conclusions needed after that
depth.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping

open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The fixed scale parameter `s₀ = 1 / 32` in the Hölder proof. -/
def holderStoppingS : ℝ := 1 / 32

theorem holderStoppingS_pos : 0 < holderStoppingS := by
  norm_num [holderStoppingS]

/-- The manuscript choice `lambda = C₁⁻¹ (1 - alpha)`. -/
def holderStoppingLambda (C1 alpha : ℝ) : ℝ :=
  C1⁻¹ * (1 - alpha)

/-- The manuscript choice `epsilon = C₂⁻¹ sqrt (1 - alpha)`. -/
def holderStoppingEpsilon (C2 alpha : ℝ) : ℝ :=
  C2⁻¹ * Real.sqrt (1 - alpha)

/-- Natural-valued readout of the manuscript's combined Hölder stopping
depth. -/
def holderStoppingScale {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (alpha lambda epsilon : ℝ)
    (step m : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℕ :=
  Int.toNat
    (regularityMinimalScale M none alpha lambda epsilon holderStoppingS step m omega)

theorem regularityMinimalScale_nonneg {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (alpha lambda epsilon s : ℝ)
    (step m : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    0 ≤ regularityMinimalScale M none alpha lambda epsilon s step m omega := by
  have herr :=
    (errorStoppingIndex M none lambda s m omega).property.2
  have hgood :=
    (goodStoppingIndex M none lambda epsilon s m omega).property.2
  unfold regularityMinimalScale
  omega

theorem holderStoppingScale_intCast {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (alpha lambda epsilon : ℝ)
    (step m : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    (holderStoppingScale M alpha lambda epsilon step m omega : ℤ) =
      regularityMinimalScale M none alpha lambda epsilon holderStoppingS step m omega := by
  unfold holderStoppingScale
  exact Int.toNat_of_nonneg
    (regularityMinimalScale_nonneg M alpha lambda epsilon holderStoppingS step m omega)

theorem holderStoppingScale_pos {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (alpha lambda epsilon : ℝ)
    (step m : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    0 < holderStoppingScale M alpha lambda epsilon step m omega := by
  have hreg : (5 : ℤ) ≤
      regularityMinimalScale M none alpha lambda epsilon holderStoppingS step m omega := by
    have herr :=
      (errorStoppingIndex M none lambda holderStoppingS m omega).property.2
    have hgood :=
      (goodStoppingIndex M none lambda epsilon holderStoppingS m omega).property.2
    unfold regularityMinimalScale
    omega
  rw [← holderStoppingScale_intCast M alpha lambda epsilon step m omega] at hreg
  omega

/-- Natural depth associated with the accumulated-error first-failure
index. -/
def errorStoppingDepth {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (lambda s : ℝ) (m : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℕ :=
  Int.toNat ((m : Int) - (errorStoppingIndex M none lambda s m omega : Int))

/-- Natural depth associated with the good-scale first-failure index. -/
def goodStoppingDepth {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (lambda epsilon s : ℝ) (m : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℕ :=
  Int.toNat ((m : Int) -
    (goodStoppingIndex M none lambda epsilon s m omega : Int))

theorem holderStoppingScale_eq_max_depth_add {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (alpha lambda epsilon : ℝ)
    (step m : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    holderStoppingScale M alpha lambda epsilon step m omega =
      max (errorStoppingDepth M lambda holderStoppingS m omega)
        (goodStoppingDepth M lambda epsilon holderStoppingS m omega) + step + 5 := by
  have herrUpper :=
    (errorStoppingIndex M none lambda holderStoppingS m omega).property.2
  have hgoodUpper :=
    (goodStoppingIndex M none lambda epsilon holderStoppingS m omega).property.2
  have herrNonneg : 0 <=
      (m : Int) - (errorStoppingIndex M none lambda holderStoppingS m omega : Int) :=
    by omega
  have hgoodNonneg : 0 <=
      (m : Int) -
        (goodStoppingIndex M none lambda epsilon holderStoppingS m omega : Int) :=
    by omega
  apply Int.ofNat_injective
  change (holderStoppingScale M alpha lambda epsilon step m omega : Int) =
    (max (errorStoppingDepth M lambda holderStoppingS m omega)
      (goodStoppingDepth M lambda epsilon holderStoppingS m omega) + step + 5 : Nat)
  rw [holderStoppingScale_intCast]
  unfold regularityMinimalScale errorStoppingDepth goodStoppingDepth
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_ofNat, Nat.cast_max,
    Int.toNat_of_nonneg herrNonneg, Int.toNat_of_nonneg hgoodNonneg]

/-- Beyond the deterministic `step + 5` shift, a large combined depth forces
one of the two constituent stopping depths to be large. -/
theorem holderStoppingScale_tail_subset {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (alpha lambda epsilon : ℝ)
    (step m k : ℕ) (hk : step + 5 <= k) :
    {omega | k < holderStoppingScale M alpha lambda epsilon step m omega} ⊆
      {omega | k - (step + 5) <
        errorStoppingDepth M lambda holderStoppingS m omega} ∪
      {omega | k - (step + 5) <
        goodStoppingDepth M lambda epsilon holderStoppingS m omega} := by
  intro omega homega
  change k < holderStoppingScale M alpha lambda epsilon step m omega at homega
  rw [holderStoppingScale_eq_max_depth_add] at homega
  simp only [Set.mem_union, Set.mem_setOf_eq]
  omega

/-- Deterministic upper bound on the literal combined stopping depth. -/
theorem holderStoppingScale_le_add {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (alpha lambda epsilon : ℝ)
    (step m : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    holderStoppingScale M alpha lambda epsilon step m omega <= m + step + 6 := by
  have herr :=
    (errorStoppingIndex M none lambda holderStoppingS m omega).property
  have hgood :=
    (goodStoppingIndex M none lambda epsilon holderStoppingS m omega).property
  have herrLower : (-1 : Int) <=
      (errorStoppingIndex M none lambda holderStoppingS m omega : Int) := herr.1
  have hgoodLower : (-1 : Int) <=
      (goodStoppingIndex M none lambda epsilon holderStoppingS m omega : Int) := hgood.1
  have hmax : max
      ((m : Int) - (errorStoppingIndex M none lambda holderStoppingS m omega : Int))
      ((m : Int) - (goodStoppingIndex M none lambda epsilon holderStoppingS m omega : Int))
      <= (m : Int) + 1 := by
    rw [max_le_iff]
    constructor <;> omega
  have hreg : regularityMinimalScale M none alpha lambda epsilon holderStoppingS
      step m omega <= ((m + step + 6 : Nat) : Int) := by
    unfold regularityMinimalScale
    calc
      max
          ((m : Int) -
            (errorStoppingIndex M none lambda holderStoppingS m omega : Int))
          ((m : Int) -
            (goodStoppingIndex M none lambda epsilon holderStoppingS m omega : Int)) +
          (step : Int) + 5 <= ((m : Int) + 1) + (step : Int) + 5 := by
        omega
      _ = ((m + step + 6 : Nat) : Int) := by push_cast; ring
  rw [← holderStoppingScale_intCast M alpha lambda epsilon step m omega] at hreg
  exact_mod_cast hreg

/-- The measurable-hull replacement of the literal combined stopping depth.
It is pointwise larger, so every pathwise post-stopping conclusion remains
valid, while each tail has no larger outer measure. -/
def measurableHolderStoppingScale {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (alpha lambda epsilon : ℝ)
    (step m : ℕ) : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d -> Nat :=
  measurableNatEnvelope M.P.toMeasure
    (holderStoppingScale M alpha lambda epsilon step m) (m + step + 6)

theorem measurable_measurableHolderStoppingScale {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (alpha lambda epsilon : ℝ)
    (step m : ℕ) :
    Measurable (measurableHolderStoppingScale M alpha lambda epsilon step m) := by
  exact measurable_measurableNatEnvelope _ _ _

theorem holderStoppingScale_le_measurable {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (alpha lambda epsilon : ℝ)
    (step m : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    holderStoppingScale M alpha lambda epsilon step m omega <=
      measurableHolderStoppingScale M alpha lambda epsilon step m omega := by
  exact le_measurableNatEnvelope
    (holderStoppingScale_le_add M alpha lambda epsilon step m omega)

theorem measurableHolderStoppingScale_pos {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (alpha lambda epsilon : ℝ)
    (step m : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    0 < measurableHolderStoppingScale M alpha lambda epsilon step m omega :=
  (holderStoppingScale_pos M alpha lambda epsilon step m omega).trans_le
    (holderStoppingScale_le_measurable M alpha lambda epsilon step m omega)

theorem measure_measurableHolderStoppingScale_tail_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (alpha lambda epsilon : ℝ)
    (step m k : ℕ) :
    M.P.toMeasure {omega |
        k < measurableHolderStoppingScale M alpha lambda epsilon step m omega} <=
      M.P.toMeasure {omega |
        k < holderStoppingScale M alpha lambda epsilon step m omega} := by
  exact measure_measurableNatEnvelope_tail_le _ _ _ _

/-- Tail union for the measurable combined scale after removing the
deterministic `step + 5` shift.  This is the carrier composition behind
`e.mathcal.L.bound.inproof`. -/
theorem measure_measurableHolderStoppingScale_tail_le_add {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (alpha lambda epsilon : ℝ)
    (step m k : ℕ) (hk : step + 5 <= k) :
    M.P.toMeasure {omega |
        k < measurableHolderStoppingScale M alpha lambda epsilon step m omega} <=
      M.P.toMeasure {omega | k - (step + 5) <
          errorStoppingDepth M lambda holderStoppingS m omega} +
        M.P.toMeasure {omega | k - (step + 5) <
          goodStoppingDepth M lambda epsilon holderStoppingS m omega} := by
  calc
    M.P.toMeasure {omega |
        k < measurableHolderStoppingScale M alpha lambda epsilon step m omega} <=
      M.P.toMeasure {omega |
        k < holderStoppingScale M alpha lambda epsilon step m omega} :=
      measure_measurableHolderStoppingScale_tail_le M alpha lambda epsilon step m k
    _ <= M.P.toMeasure
          ({omega | k - (step + 5) <
              errorStoppingDepth M lambda holderStoppingS m omega} ∪
            {omega | k - (step + 5) <
              goodStoppingDepth M lambda epsilon holderStoppingS m omega}) :=
      MeasureTheory.measure_mono
        (holderStoppingScale_tail_subset M alpha lambda epsilon step m k hk)
    _ <= M.P.toMeasure {omega | k - (step + 5) <
          errorStoppingDepth M lambda holderStoppingS m omega} +
        M.P.toMeasure {omega | k - (step + 5) <
          goodStoppingDepth M lambda epsilon holderStoppingS m omega} :=
      MeasureTheory.measure_union_le _ _

/-- Once the scale gap exceeds the combined stopping depth, both frozen
first-failure indices lie below the current scale. -/
theorem le_stoppingIndices_of_holderStoppingScale_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (alpha lambda epsilon : ℝ)
    (step m n : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hn : (holderStoppingScale M alpha lambda epsilon step m omega : ℤ) ≤
      (m : ℤ) - (n : ℤ)) :
    (n : ℤ) ≤ errorStoppingIndex M none lambda holderStoppingS m omega ∧
      (n : ℤ) ≤
        goodStoppingIndex M none lambda epsilon holderStoppingS m omega := by
  rw [holderStoppingScale_intCast] at hn
  unfold regularityMinimalScale at hn
  constructor <;> omega

/-- Step 2 of the Hölder proof: beyond the combined random depth, the
accumulated error and the number of bad good-event scales satisfy their exact
printed bounds simultaneously at every admissible grid centre. -/
theorem holder_stopped_controls {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (alpha lambda epsilon : ℝ)
    (step m n : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hn : (holderStoppingScale M alpha lambda epsilon step m omega : ℤ) ≤
      (m : ℤ) - (n : ℤ))
    (z : Vec d) (hzgrid : OnTriadicGrid n z) (hzmem : z ∈ cube d m) :
    (∑ j ∈ Finset.Icc n m, accumulatedError M none j z holderStoppingS omega) ≤
        lambda * ((m : ℝ) - (n : ℝ)) ∧
      (∑ j ∈ Finset.Icc n m,
          (1 - if omega ∈ goodEvent M none j z epsilon holderStoppingS then
            1 else 0)) <
        1 + lambda * ((m : ℝ) - (n : ℝ)) := by
  obtain ⟨herr, hgood⟩ :=
    le_stoppingIndices_of_holderStoppingScale_le
      M alpha lambda epsilon step m n omega hn
  exact ⟨
    accumulatedError_sum_le_of_le_errorStoppingIndex
      M none lambda holderStoppingS m n omega herr z hzgrid hzmem,
    badScaleCount_lt_of_le_goodStoppingIndex
      M none lambda epsilon holderStoppingS m n omega hgood z hzgrid hzmem⟩

/-- The pathwise stopping conclusions with the exact Hölder parameter choices
substituted.  This is the direct Lean form of display
`e.after.good.scales.applied`. -/
theorem holder_stopped_controls_at_parameters {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (C1 C2 alpha : ℝ)
    (step m n : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hn : (holderStoppingScale M alpha (holderStoppingLambda C1 alpha)
        (holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
      (m : ℤ) - (n : ℤ))
    (z : Vec d) (hzgrid : OnTriadicGrid n z) (hzmem : z ∈ cube d m) :
    (∑ j ∈ Finset.Icc n m, accumulatedError M none j z holderStoppingS omega) ≤
        holderStoppingLambda C1 alpha * ((m : ℝ) - (n : ℝ)) ∧
      (∑ j ∈ Finset.Icc n m,
          (1 - if omega ∈ goodEvent M none j z
            (holderStoppingEpsilon C2 alpha) holderStoppingS then 1 else 0)) <
        1 + holderStoppingLambda C1 alpha * ((m : ℝ) - (n : ℝ)) := by
  exact holder_stopped_controls M alpha (holderStoppingLambda C1 alpha)
    (holderStoppingEpsilon C2 alpha) step m n omega hn z hzgrid hzmem

/-- The two exact post-stopping controls for the measurable replacement of
the literal Hölder depth. -/
theorem measurableHolder_stopped_controls_at_parameters {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (C1 C2 alpha : ℝ)
    (step m n : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hn : (measurableHolderStoppingScale M alpha
        (holderStoppingLambda C1 alpha) (holderStoppingEpsilon C2 alpha)
        step m omega : Int) <= (m : Int) - (n : Int))
    (z : Vec d) (hzgrid : OnTriadicGrid n z) (hzmem : z ∈ cube d m) :
    (∑ j ∈ Finset.Icc n m, accumulatedError M none j z holderStoppingS omega) <=
        holderStoppingLambda C1 alpha * ((m : Real) - (n : Real)) ∧
      (∑ j ∈ Finset.Icc n m,
          (1 - if omega ∈ goodEvent M none j z
            (holderStoppingEpsilon C2 alpha) holderStoppingS then 1 else 0)) <
        1 + holderStoppingLambda C1 alpha * ((m : Real) - (n : Real)) := by
  have hle := holderStoppingScale_le_measurable M alpha
    (holderStoppingLambda C1 alpha) (holderStoppingEpsilon C2 alpha) step m omega
  have hraw : (holderStoppingScale M alpha (holderStoppingLambda C1 alpha)
      (holderStoppingEpsilon C2 alpha) step m omega : Int) <=
      (m : Int) - (n : Int) := (Int.ofNat_le.2 hle).trans hn
  exact holder_stopped_controls_at_parameters M C1 C2 alpha step m n omega
    hraw z hzgrid hzmem

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
