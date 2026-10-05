module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.Windows


-- Adapted from the boundary windows of Algsuperdiff/Section4/Provider/ExcessDecay

@[expose] public section

/-!
# The boundary window as an open bounded convex domain

The datum argument solves a Dirichlet problem on the window `U_{m,k}(x)`, and every
existence and Poincaré input of CoarseGraining is stated for an
`IsOpenBoundedConvexDomain`.  This module supplies that packaging — the window
is an intersection of a translate of an open cube with an open cube — together
with the positivity of its volume, which the residual-corrector existence
consumes as nonemptiness.

Nothing here is an estimate: every statement is geometry.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum

open MeasureTheory
open Homogenization (Vec openCubeSet originCube translateSet IsOpenBoundedConvexDomain)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder

noncomputable section

variable {d : ℕ}

/-! ### Translating a set -/

/-- The pointwise translate `y ↦ z + y` of a set is CoarseGraining's
`translateSet`. -/
theorem image_add_eq_translateSet (z : Vec d) (U : Set (Vec d)) :
    (fun y => z + y) '' U = translateSet z U := by
  ext p
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, add_comm z y⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, add_comm z y⟩

/-! ### The window is an open bounded convex domain -/

/-- The intersection of two open bounded convex domains is one: openness and
convexity are stable under intersection, and the bound of either factor serves. -/
theorem isOpenBoundedConvexDomain_inter {U V : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hV : IsOpenBoundedConvexDomain V) :
    IsOpenBoundedConvexDomain (U ∩ V) := by
  obtain ⟨R, hRpos, hR⟩ := hU.isBoundedDomain
  exact ⟨hU.isOpen.inter hV.isOpen, ⟨R, hRpos, fun y hy i => hR y hy.1 i⟩,
    hU.convex.inter hV.convex⟩

/-- **The boundary argument's window is an open bounded convex domain.** -/
theorem isOpenBoundedConvexDomain_truncatedWindow (x : Vec d) (m k : ℤ) :
    IsOpenBoundedConvexDomain (truncatedWindow x m k) := by
  refine isOpenBoundedConvexDomain_inter ?_
    (Homogenization.isOpenBoundedConvexDomain_openCubeSet _)
  rw [image_add_eq_translateSet]
  exact (Homogenization.isOpenBoundedConvexDomain_openCubeSet (originCube d k)).translateSet x

/-- A window centred in the domain cube has positive volume: it is a nonempty
open set. -/
theorem volume_truncatedWindow_pos {x : Vec d} {m : ℤ} (k : ℤ)
    (hx : x ∈ openCubeSet (originCube d m)) :
    0 < volume (truncatedWindow x m k) :=
  (isOpen_truncatedWindow x m k).measure_pos volume (truncatedWindow_nonempty k hx)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum
