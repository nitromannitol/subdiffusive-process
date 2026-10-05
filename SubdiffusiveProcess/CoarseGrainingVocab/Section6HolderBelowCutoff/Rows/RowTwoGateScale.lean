module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.GateParameters
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.GateParameters
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.TopGoodScale
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.TopGoodScale
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.WindowContainment
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.RowOneInstantiation

@[expose] public section

/-!
# The gate scale row 2 runs interior Step 6 at

Interior Step 6 reads its good event **six scales above** the scale at which its
conclusion lands: the good event sits at `gate + 2` and the energy is controlled
on `U_{m,gate-4}`.  Row 2's conclusion must land at the frozen base scale `n`,
so the gate has to be run at some `gate ≥ n + 4` — and no selection at the base
scale itself can produce that.

`TopGoodScale.exists_goodScale_in_window_cut` is exactly the tool: the stopped
failure row at the base scale `n` is read over `Icc n m`, and a *sub-window*
`[n+6, n+6+K]` with more scales than the failure budget must contain a good
scale.  Taking `gate := q - 2` for such a `q` gives `n + 4 ≤ gate ≤ n + 4 + K`,
and `GateParameters.goodEvent_gate_of_selection_cut` converts the selection's good
event into the gate's own parameters (`epsilon ↦ 1`, `s ↦ s/8`, an equality of
the two stopping constants, not an estimate).
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows

open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}
variable {L : ℕ}

/-- Membership in a truncated window from a strict coordinate bound. -/
theorem mem_truncatedCube_of_dist_cut {m j : ℤ} {x z : Vec d} (hx : x ∈ cube d m)
    (hdist : ∀ i : Fin d, |x i - z i| < (1 / 2 : ℝ) * (3 : ℝ) ^ j) :
    x ∈ truncatedCube d m j z := by
  refine ⟨?_, hx⟩
  refine Section6ExcessDecay.mem_translatedCube_iff.mpr ?_
  show x - z ∈ openCubeSet (originCube d j)
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have h := abs_lt.mp (hdist i)
  simp only [Pi.sub_apply]
  constructor <;> linarith only [h.1, h.2]

/-- **The gate scale.**  A selected scale at least four above the base, at which
interior Step 6's good event holds in the gate's own parameters. -/
theorem exists_interiorRowTwoGateScale_cut (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (C1 C2 alpha : ℝ) (step m n K : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z : Vec d)
    (hzgrid : OnTriadicGrid n z) (hz : z ∈ cube d m)
    (hstop : (Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
        (Section6Stopping.holderStoppingLambda C1 alpha)
        (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
      (m : ℤ) - (n : ℤ))
    (hC2 : 1 ≤ C2) (halpha0 : 1 / 2 ≤ alpha)
    (hwin : n + K + 6 ≤ m)
    (hroom : Section6Stopping.holderStoppingLambda C1 alpha *
      ((m : ℝ) - (n : ℝ)) ≤ (K : ℝ)) :
    ∃ gate : ℕ, n + 4 ≤ gate ∧ gate ≤ n + 4 + K ∧
      omega ∈ goodEvent M (some L) (gate + 2) z 1
        ((interiorFractionalOrder_cut).1 / 8) := by
  obtain ⟨hcY, _⟩ := stoppedControls_pair_cut M C1 C2 alpha step m n omega hstop
    z hzgrid hz
  have hfail := hcY.2
  have hroom' : 1 + Section6Stopping.holderStoppingLambda C1 alpha *
      ((m : ℝ) - (n : ℝ)) ≤ ((n + 6 + K : ℕ) : ℝ) - ((n + 6 : ℕ) : ℝ) + 1 := by
    push_cast
    linarith
  obtain ⟨q, hq, hgood⟩ := exists_goodScale_in_window_cut M
    (Section6Stopping.holderStoppingEpsilon C2 alpha)
    Section6Stopping.holderStoppingS
    (Section6Stopping.holderStoppingLambda C1 alpha)
    (n := n) (m := m) (a := n + 6) (b := n + 6 + K)
    (by omega) (by omega) (by omega) z omega hfail hroom'
  rw [Finset.mem_Icc] at hq
  obtain ⟨gate, rfl⟩ : ∃ gate : ℕ, q = gate + 2 := ⟨q - 2, by omega⟩
  exact ⟨gate, by omega, by omega,
    goodEvent_gate_of_selection_cut M hC2 halpha0 gate z hgood⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows
