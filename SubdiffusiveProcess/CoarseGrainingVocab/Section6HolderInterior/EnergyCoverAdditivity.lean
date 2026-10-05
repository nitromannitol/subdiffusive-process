module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.WindowContainment

@[expose] public section

/-!
# Energy additivity over a cover

The cover belongs on row 2's **energy**, not on
row 1's oscillation.  Energies carry no mean, so a cover costs nothing but the
box count — this file supplies that step.

`setIntegral_union_le` is the whole mechanism; everything else is bookkeeping.
Contrast the oscillation, where the same move is *false* because each window
subtracts its own mean.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section

variable {d : ℕ}

/-- **Energy additivity over a two-set union.**  For a nonnegative integrand the
integral over a union is at most the sum of the integrals. -/
theorem setIntegral_union_le {A B : Set (Vec d)} {g : Vec d → ℝ}
    (hAmeas : MeasurableSet A) (hBmeas : MeasurableSet B)
    (hg0 : ∀ p, 0 ≤ g p)
    (hgA : IntegrableOn g A volume) (hgB : IntegrableOn g B volume) :
    ∫ p in A ∪ B, g p ∂volume ≤
      ∫ p in A, g p ∂volume + ∫ p in B, g p ∂volume := by
  have hunion : A ∪ B = A ∪ (B \ A) := by
    ext p
    by_cases hp : p ∈ A <;> simp [hp]
  have hdiffMeas : MeasurableSet (B \ A) := hBmeas.diff hAmeas
  have hgdiff : IntegrableOn g (B \ A) volume := hgB.mono_set Set.sdiff_subset
  have hmono : ∫ p in B \ A, g p ∂volume ≤ ∫ p in B, g p ∂volume := by
    refine setIntegral_mono_set hgB (Filter.Eventually.of_forall hg0) ?_
    exact Filter.Eventually.of_forall (fun p hp => hp.1)
  rw [hunion, setIntegral_union Set.disjoint_sdiff_right hdiffMeas hgA hgdiff]
  linarith

/-- The same for anything inside the union. -/
theorem setIntegral_le_of_cover_two {W A B : Set (Vec d)} {g : Vec d → ℝ}
    (hAmeas : MeasurableSet A) (hBmeas : MeasurableSet B)
    (hcover : W ⊆ A ∪ B) (hg0 : ∀ p, 0 ≤ g p)
    (hgA : IntegrableOn g A volume) (hgB : IntegrableOn g B volume) :
    ∫ p in W, g p ∂volume ≤
      ∫ p in A, g p ∂volume + ∫ p in B, g p ∂volume := by
  have hgU : IntegrableOn g (A ∪ B) volume := hgA.union hgB
  have hmono : ∫ p in W, g p ∂volume ≤ ∫ p in A ∪ B, g p ∂volume := by
    refine setIntegral_mono_set hgU (Filter.Eventually.of_forall hg0) ?_
    exact Filter.Eventually.of_forall (fun p hp => hcover hp)
  exact hmono.trans (setIntegral_union_le hAmeas hBmeas hg0 hgA hgB)

/-- The integral over a finite union is at most the sum over the family. -/
theorem setIntegral_biUnion_le {ι : Type*} [DecidableEq ι] (S : Finset ι)
    {Wf : ι → Set (Vec d)} {g : Vec d → ℝ}
    (hmeas : ∀ y, MeasurableSet (Wf y)) (hg0 : ∀ p, 0 ≤ g p)
    (hint : ∀ y, IntegrableOn g (Wf y) volume) :
    ∫ p in ⋃ y ∈ S, Wf y, g p ∂volume ≤
      ∑ y ∈ S, ∫ p in Wf y, g p ∂volume := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a T ha iht =>
      have hTmeas : MeasurableSet (⋃ y ∈ T, Wf y) :=
        Set.Finite.measurableSet_biUnion T.finite_toSet (fun y _ => hmeas y)
      have hTint : IntegrableOn g (⋃ y ∈ T, Wf y) volume :=
        integrableOn_finset_iUnion.mpr (fun y _ => hint y)
      have hstep : ∫ p in Wf a ∪ (⋃ y ∈ T, Wf y), g p ∂volume ≤
          ∫ p in Wf a, g p ∂volume + ∫ p in ⋃ y ∈ T, Wf y, g p ∂volume :=
        setIntegral_union_le (hmeas a) hTmeas hg0 (hint a) hTint
      rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
      linarith

/-- **Energy additivity over a finite cover.** -/
theorem setIntegral_le_of_cover_finset {W : Set (Vec d)} {ι : Type*}
    [DecidableEq ι] {S : Finset ι} {Wf : ι → Set (Vec d)} {g : Vec d → ℝ}
    (hmeas : ∀ y, MeasurableSet (Wf y)) (hg0 : ∀ p, 0 ≤ g p)
    (hint : ∀ y, IntegrableOn g (Wf y) volume)
    (hcover : W ⊆ ⋃ y ∈ S, Wf y) :
    ∫ p in W, g p ∂volume ≤ ∑ y ∈ S, ∫ p in Wf y, g p ∂volume := by
  have hUint : IntegrableOn g (⋃ y ∈ S, Wf y) volume :=
    integrableOn_finset_iUnion.mpr (fun y _ => hint y)
  have hmono : ∫ p in W, g p ∂volume ≤ ∫ p in ⋃ y ∈ S, Wf y, g p ∂volume := by
    refine setIntegral_mono_set hUint (Filter.Eventually.of_forall hg0) ?_
    exact Filter.Eventually.of_forall (fun p hp => hcover hp)
  exact hmono.trans (setIntegral_biUnion_le S hmeas hg0 hint)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
