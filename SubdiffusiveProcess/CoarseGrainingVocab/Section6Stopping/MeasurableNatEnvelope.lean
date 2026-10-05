module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping

open MeasureTheory

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The nested measurable hull of the first `k + 1` tails of `R`. -/
def natTailHull {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (R : Omega -> Nat) (k : Nat) : Set Omega :=
  {omega | forall j : {j : Nat // j <= k},
    omega ∈ toMeasurable mu {omega | j.1 < R omega}}

theorem measurableSet_natTailHull {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (R : Omega -> Nat) (k : Nat) :
    MeasurableSet (natTailHull mu R k) := by
  rw [show natTailHull mu R k = ⋂ j : {j : Nat // j <= k},
      toMeasurable mu {omega | j.1 < R omega} by
    ext omega
    simp only [natTailHull, Set.mem_ofPred_eq, Set.mem_iInter]]
  exact MeasurableSet.iInter fun j => measurableSet_toMeasurable _ _

theorem mem_natTailHull_of_lt {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {R : Omega -> Nat} {omega : Omega} {k : Nat}
    (hk : k < R omega) : omega ∈ natTailHull mu R k := by
  intro j
  exact subset_toMeasurable mu _ (lt_of_le_of_lt j.2 hk)

theorem natTailHull_subset_toMeasurable_tail {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega) (R : Omega -> Nat) (k : Nat) :
    natTailHull mu R k ⊆ toMeasurable mu {omega | k < R omega} := by
  intro omega homega
  exact homega ⟨k, le_rfl⟩

theorem natTailHull_antitone {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {R : Omega -> Nat} {j k : Nat} (hjk : j <= k) :
    natTailHull mu R k ⊆ natTailHull mu R j := by
  intro omega homega i
  exact homega ⟨i.1, i.2.trans hjk⟩

/-- A bounded measurable envelope of an arbitrary natural-valued map.

At stage `B + 1` it takes the value `B + 1` on the measurable hull of the
`B`th tail and otherwise retains the preceding envelope. -/
def measurableNatEnvelope {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (R : Omega -> Nat) : Nat -> Omega -> Nat
  | 0 => fun _ => 0
  | B + 1 => fun omega =>
      if omega ∈ natTailHull mu R B then B + 1
      else measurableNatEnvelope mu R B omega

theorem measurable_measurableNatEnvelope {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega) (R : Omega -> Nat) (B : Nat) :
    Measurable (measurableNatEnvelope mu R B) := by
  induction B with
  | zero => exact measurable_const
  | succ B ih =>
      exact Measurable.piecewise (measurableSet_natTailHull mu R B)
        measurable_const ih

theorem measurableNatEnvelope_le {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (R : Omega -> Nat) (B : Nat) (omega : Omega) :
    measurableNatEnvelope mu R B omega <= B := by
  induction B with
  | zero => simp [measurableNatEnvelope]
  | succ B ih =>
      simp only [measurableNatEnvelope]
      split_ifs
      · exact le_rfl
      · exact ih.trans (Nat.le_succ B)

theorem le_measurableNatEnvelope {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {R : Omega -> Nat} {B : Nat} {omega : Omega}
    (hRB : R omega <= B) : R omega <= measurableNatEnvelope mu R B omega := by
  induction B with
  | zero =>
      have hR : R omega = 0 := Nat.eq_zero_of_le_zero hRB
      simp [hR, measurableNatEnvelope]
  | succ B ih =>
      by_cases htop : R omega = B + 1
      · have hmem : omega ∈ natTailHull mu R B :=
          mem_natTailHull_of_lt (by omega)
        simp [measurableNatEnvelope, hmem, htop]
      · have hRle : R omega <= B := by omega
        simp only [measurableNatEnvelope]
        split_ifs
        · exact hRle.trans (Nat.le_succ B)
        · exact ih hRle

theorem measurableNatEnvelope_tail_subset {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega} {R : Omega -> Nat}
    (B k : Nat) :
    {omega | k < measurableNatEnvelope mu R B omega} ⊆ natTailHull mu R k := by
  induction B with
  | zero =>
      intro omega homega
      simp [measurableNatEnvelope] at homega
  | succ B ih =>
      intro omega homega
      change k < measurableNatEnvelope mu R (B + 1) omega at homega
      simp only [measurableNatEnvelope] at homega
      by_cases hB : omega ∈ natTailHull mu R B
      · rw [ite_eq_left hB] at homega
        exact natTailHull_antitone (by omega) hB
      · rw [ite_eq_right hB] at homega
        exact ih homega

/-- Every tail of the measurable envelope has outer measure no larger than
the corresponding tail of the original, possibly nonmeasurable, map. -/
theorem measure_measurableNatEnvelope_tail_le {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega) (R : Omega -> Nat)
    (B k : Nat) :
    mu {omega | k < measurableNatEnvelope mu R B omega} <=
      mu {omega | k < R omega} := by
  calc
    mu {omega | k < measurableNatEnvelope mu R B omega} <=
        mu (natTailHull mu R k) :=
      measure_mono (measurableNatEnvelope_tail_subset B k)
    _ <= mu (toMeasurable mu {omega | k < R omega}) :=
      measure_mono (natTailHull_subset_toMeasurable_tail mu R k)
    _ = mu {omega | k < R omega} := measure_toMeasurable _

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
