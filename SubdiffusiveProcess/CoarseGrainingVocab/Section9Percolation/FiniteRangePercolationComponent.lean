import SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation.FiniteRangePercolationGeometry

/-!
# Elementary facts about finite-step components

The corrected percolation carrier represents a bad component by finite `J`-step paths.
This file proves the endpoint and meeting properties used by the component-diameter clause.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

open Set

noncomputable section

variable {d J : ℕ} {S B : Set (Lattice d)} {v w : Lattice d}



theorem mem_of_jStepReachableIn (h : JStepReachableIn J S v w) : w ∈ S := by
  obtain ⟨path, _hhead, hlast, _hstep, hmem⟩ := h
  have hwOption : w ∈ path.getLast? := by
    rw [hlast]
    simp only [Option.mem_some_iff]
  obtain ⟨hne, hwlast⟩ := List.mem_getLast?_eq_getLast hwOption
  rw [hwlast]
  exact hmem _ (List.getLast_mem hne)



theorem jStepReachableIn_self_iff : JStepReachableIn J S v v ↔ v ∈ S := by
  constructor
  · exact mem_of_jStepReachableIn
  · intro hv
    refine ⟨[v], rfl, rfl, ?_, ?_⟩
    · intro k hk
      simp only [List.length_cons, List.length_nil] at hk
      omega
    · intro u hu
      simp only [List.mem_singleton] at hu
      exact hu ▸ hv



theorem jStepComponent_subset : jStepComponent J S v ⊆ S := by
  intro u hu
  exact mem_of_jStepReachableIn hu



theorem jStepComponent_inter_nonempty (hvS : v ∈ S) (hvB : v ∈ B) :
    (jStepComponent J S v ∩ B).Nonempty :=
  ⟨v, jStepReachableIn_self_iff.mpr hvS, hvB⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
