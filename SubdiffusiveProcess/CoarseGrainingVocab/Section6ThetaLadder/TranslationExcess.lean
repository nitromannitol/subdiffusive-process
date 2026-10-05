module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorTransport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.ScaledInterface

@[expose] public section

/-!
# Theta-perturbed ladder: translation of affine excess

The product recurrence is proved on origin cubes.  These deterministic
identities transport its affine competitors and its scale-normalized excess
to the translated cubes used by the bounded-multiplier cover.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open Homogenization MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration

noncomputable section

variable {d : ℕ}

/-- Translating the window changes only the affine intercept. -/
theorem affineDistOn_translateSet (z : Vec d) (U : Set (Vec d))
    (f : Vec d → ℝ) (c : ℝ) (g : Vec d) :
    affineDistOn (translateSet z U) f c g =
      affineDistOn U (fun x ↦ f (x + z)) (c + vecDot g z) g := by
  unfold affineDistOn
  rw [normalizedL2On_translateSet]
  congr 1
  funext x
  unfold affineEval
  rw [vecDot_add_right]
  ring

/-- The full set of affine errors is translation invariant after the
bijective intercept change. -/
theorem affineDistSet_translateSet (z : Vec d) (U : Set (Vec d))
    (f : Vec d → ℝ) :
    affineDistSet (translateSet z U) f =
      affineDistSet U (fun x ↦ f (x + z)) := by
  ext r
  constructor
  · rintro ⟨p, rfl⟩
    change affineDistOn (translateSet z U) f p.1 p.2 ∈ _
    rw [affineDistOn_translateSet]
    exact ⟨(p.1 + vecDot p.2 z, p.2), rfl⟩
  · rintro ⟨p, rfl⟩
    refine ⟨(p.1 - vecDot p.2 z, p.2), ?_⟩
    change affineDistOn (translateSet z U) f
      (p.1 - vecDot p.2 z) p.2 = _
    rw [affineDistOn_translateSet]
    congr 2
    ring

theorem affineExcessRaw_translateSet (z : Vec d) (U : Set (Vec d))
    (f : Vec d → ℝ) :
    affineExcessRaw (translateSet z U) f =
      affineExcessRaw U (fun x ↦ f (x + z)) := by
  unfold affineExcessRaw
  rw [affineDistSet_translateSet]

/-- Frozen scale-normalized excess is invariant under translation. -/
theorem excess_translateSet (j : ℤ) (z : Vec d) (U : Set (Vec d))
    (f : Vec d → ℝ) :
    excess j (translateSet z U) f =
      excess j U (fun x ↦ f (x + z)) := by
  rw [excess_eq_affineExcessScaled, excess_eq_affineExcessScaled]
  unfold affineExcessScaled
  rw [affineExcessRaw_translateSet]

/-- Affine minimizers transport with the same slope and the translated
intercept. -/
theorem mem_affineMinimizers_translateSet_iff
    (z : Vec d) (U : Set (Vec d)) (f : Vec d → ℝ)
    (c : ℝ) (g : Vec d) :
    (⟨c, g⟩ : Affine d) ∈ affineMinimizers (translateSet z U) f ↔
      (⟨c + vecDot g z, g⟩ : Affine d) ∈
        affineMinimizers U (fun x ↦ f (x + z)) := by
  rw [mem_affineMinimizers_iff, mem_affineMinimizers_iff]
  unfold IsAffineMinimizer
  rw [affineDistOn_translateSet, affineExcessRaw_translateSet]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
