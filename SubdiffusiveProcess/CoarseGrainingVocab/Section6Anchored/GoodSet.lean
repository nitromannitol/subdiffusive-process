module

public import SubdiffusiveProcess.Assumptions.AnchoredCoefficient

@[expose] public section

/-!
# The anchored good event as a plain existence event
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored

open Filter _root_.SubdiffusiveProcess.Model Homogenization Topology

variable {d : ℕ}

/-- The anchored local `C¹ˑ¹` limit is unique as soon as it exists: the value
sequence converges uniformly on every singleton, so its limit is determined
pointwise, and a potential field is determined by its values. -/
theorem isAnchoredC11Limit_unique {omega : PotentialSample d}
    {g h : PotentialField d} (hg : IsAnchoredC11Limit omega g)
    (hh : IsAnchoredC11Limit omega h) : g = h := by
  refine _root_.SubdiffusiveProcess.Model.PotentialField.ext fun x => ?_
  have hgx := (hg.value_tendsto {x} isCompact_singleton).tendsto_at rfl
  have hhx := (hh.value_tendsto {x} isCompact_singleton).tendsto_at rfl
  exact tendsto_nhds_unique hgx hhx

/-- On the canonical carrier the `∃!` event is the plain existence event. -/
theorem anchoredC11GoodSet_eq :
    anchoredC11GoodSet d = {omega | ∃ g : PotentialField d,
      IsAnchoredC11Limit omega g} := by
  ext omega
  simp only [anchoredC11GoodSet, Set.mem_ofPred_eq]
  exact ⟨fun h => h.exists, fun ⟨g, hg⟩ =>
    ⟨g, hg, fun h hh => isAnchoredC11Limit_unique hh hg⟩⟩

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
