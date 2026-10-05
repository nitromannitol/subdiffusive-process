module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionGraphDistance
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRepairedConnected

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Set
open Homogenization

noncomputable section

variable {d : ℕ} [NeZero d] {Omega : Type*} {base : ℤ}
variable {failure : TriadicCube d → Set Omega} {omega : Omega}

/-- A fixed-sample short crossing of a Euclidean exterior by fewer than the
prescribed number of repaired-graph steps. -/
def RepairedStoppingShortCrossing
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty) (x0 : Vec d) (R epsilon : ℝ) (k : ℕ) :
    Prop :=
  ∃ q : RefinedStoppingCell failure omega base,
    (translatedCube d (refinedStoppingScale q) (refinedStoppingCenter q) ∩
      (Metric.ball x0 ((3 : ℝ) ^ k * R))ᶜ).Nonempty ∧
      stoppingGraphDistance repairedStoppingGraph source hsource q <
        ⌈epsilon * (3 : ℝ) ^ k⌉₊

/-- Along an edge of the repaired graph, distance from a fixed source can
decrease by at most one. -/
theorem repairedStoppingGraphDistance_le_succ_of_adj
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty) {q p : RefinedStoppingCell failure omega base}
    (hadj : repairedStoppingGraph.Adj q p) :
    stoppingGraphDistance repairedStoppingGraph source hsource q ≤
      stoppingGraphDistance repairedStoppingGraph source hsource p + 1 :=
  stoppingGraphDistance_le_succ_of_adj repairedStoppingGraph
    (repairedStoppingGraph_connected failure omega hinitial hrepair)
    hsource hadj

omit [NeZero d] in
/-- Outside the fixed-sample short-crossing predicate, an exterior cell is at
least the prescribed number of repaired-graph steps from the source. -/
theorem natCeil_le_repairedStoppingGraphDistance_of_not_shortCrossing
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty) (x0 : Vec d) (R epsilon : ℝ) {k : ℕ}
    (hgood : ¬ RepairedStoppingShortCrossing source hsource x0 R epsilon k)
    {q : RefinedStoppingCell failure omega base}
    (hmeet :
      (translatedCube d (refinedStoppingScale q) (refinedStoppingCenter q) ∩
        (Metric.ball x0 ((3 : ℝ) ^ k * R))ᶜ).Nonempty) :
    ⌈epsilon * (3 : ℝ) ^ k⌉₊ ≤
      stoppingGraphDistance repairedStoppingGraph source hsource q := by
  by_contra hnot
  exact hgood ⟨q, hmeet, Nat.lt_of_not_ge hnot⟩

omit [NeZero d] in
/-- Real-valued graph-distance lower bound for every repaired cell meeting a
radius-`r` exterior.  The loss of three is the passage to the preceding
triadic radius. -/
theorem repairedStoppingGraphDistance_lower_bound_of_not_shortCrossing
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty) (x0 : Vec d)
    {R epsilon r : ℝ} (hR : 0 < R) (hepsilon : 0 ≤ epsilon) {k : ℕ}
    (hlower : (3 : ℝ) ^ k * R ≤ r)
    (hupper : r ≤ 3 * ((3 : ℝ) ^ k * R))
    (hgood : ¬ RepairedStoppingShortCrossing source hsource x0 R epsilon k)
    {q : RefinedStoppingCell failure omega base}
    (hmeet :
      (translatedCube d (refinedStoppingScale q) (refinedStoppingCenter q) ∩
        (Metric.ball x0 r)ᶜ).Nonempty) :
    epsilon * r / (3 * R) ≤
      stoppingGraphDistance repairedStoppingGraph source hsource q := by
  have hR3 : 0 < 3 * R := mul_pos (by norm_num) hR
  have hsmallBall :
      Metric.ball x0 ((3 : ℝ) ^ k * R) ⊆ Metric.ball x0 r :=
    Metric.ball_subset_ball hlower
  obtain ⟨x, hxcell, hxoutside⟩ := hmeet
  have hmeetScale :
      (translatedCube d (refinedStoppingScale q) (refinedStoppingCenter q) ∩
        (Metric.ball x0 ((3 : ℝ) ^ k * R))ᶜ).Nonempty :=
    ⟨x, hxcell, fun hx ↦ hxoutside (hsmallBall hx)⟩
  have hnat :=
    natCeil_le_repairedStoppingGraphDistance_of_not_shortCrossing source
      hsource x0 R epsilon hgood hmeetScale
  have hceil : epsilon * (3 : ℝ) ^ k ≤
      (⌈epsilon * (3 : ℝ) ^ k⌉₊ : ℝ) := Nat.le_ceil _
  calc
    epsilon * r / (3 * R) ≤ epsilon * (3 : ℝ) ^ k := by
      rw [div_le_iff₀ hR3]
      nlinarith [show (0 : ℝ) ≤ (3 : ℝ) ^ k by positivity]
    _ ≤ (⌈epsilon * (3 : ℝ) ^ k⌉₊ : ℕ) := hceil
    _ ≤ stoppingGraphDistance repairedStoppingGraph source hsource q := by
      exact_mod_cast hnat

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
