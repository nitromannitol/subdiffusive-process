module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation.FiniteRangePercolationComponent

@[expose] public section

/-!
# Connectivity of finite-step components

This file proves that the finite-list reachability relation used for the Section 9 bad-site
components is symmetric and transitive.  Consequently, changing the root within a component
does not change the component.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

open Set

noncomputable section

variable {d J : ℕ} {S : Set (Lattice d)} {u v w : Lattice d}

/-- The index-based finite-step path predicate is the standard adjacent-list chain.

Source: the `J`-step path convention.
-/
theorem isJStepListPath_iff_isChain (path : List (Lattice d)) :
    IsJStepListPath J path ↔
      path.IsChain fun x y ↦ latticeDist x y ≤ J := by
  rw [List.isChain_iff_getElem]
  constructor
  · intro h i hi
    simpa only [← getElem!_pos] using h i hi
  · intro h i hi
    simpa only [← getElem!_pos] using h i hi

/-- Finite-step reachability inside a fixed site set is symmetric.

Source: the `J`-step connected-component clause.
-/
theorem JStepReachableIn.symm (h : JStepReachableIn J S v w) :
    JStepReachableIn J S w v := by
  obtain ⟨path, hhead, hlast, hstep, hmem⟩ := h
  refine ⟨path.reverse, ?_, ?_, ?_, ?_⟩
  · simpa only [List.head?_reverse] using hlast
  · simpa only [List.getLast?_reverse] using hhead
  · apply (isJStepListPath_iff_isChain path.reverse).mpr
    apply List.isChain_reverse.mpr
    apply (isJStepListPath_iff_isChain path).mp hstep |>.imp
    intro x y hxy
    rw [latticeDist_comm]
    exact hxy
  · intro x hx
    exact hmem x (List.mem_reverse.mp hx)

/-- Finite-step reachability inside a fixed site set is transitive.

Source: the `J`-step connected-component clause.
-/
theorem JStepReachableIn.trans (hvw : JStepReachableIn J S v w)
    (hwu : JStepReachableIn J S w u) : JStepReachableIn J S v u := by
  obtain ⟨path, hhead, hlast, hstep, hmem⟩ := hvw
  obtain ⟨path', hhead', hlast', hstep', hmem'⟩ := hwu
  have hne : path ≠ [] := by
    intro hempty
    rw [hempty] at hhead
    simp at hhead
  have hne' : path' ≠ [] := by
    intro hempty
    rw [hempty] at hhead'
    simp at hhead'
  refine ⟨path ++ path', ?_, ?_, ?_, ?_⟩
  · rw [List.head?_append_of_ne_nil path hne, hhead]
  · rw [List.getLast?_append_of_ne_nil path hne', hlast']
  · apply (isJStepListPath_iff_isChain (path ++ path')).mpr
    apply List.IsChain.append
    · exact (isJStepListPath_iff_isChain path).mp hstep
    · exact (isJStepListPath_iff_isChain path').mp hstep'
    · intro x hx y hy
      have hxw : x = w := by
        rw [hlast] at hx
        exact (Option.mem_some_iff.mp hx).symm
      have hyw : y = w := by
        rw [hhead'] at hy
        exact (Option.mem_some_iff.mp hy).symm
      rw [hxw, hyw, latticeDist_self]
      exact Nat.zero_le J
  · intro x hx
    rw [List.mem_append] at hx
    exact hx.elim (hmem x) (hmem' x)

/-- Rooting a finite-step component at any of its members gives the same set.

Source: the connected-component interpretation.
-/
theorem jStepComponent_eq_of_mem (hw : w ∈ jStepComponent J S v) :
    jStepComponent J S w = jStepComponent J S v := by
  ext x
  constructor
  · intro hx
    exact hw.trans hx
  · intro hx
    exact hw.symm.trans hx

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
