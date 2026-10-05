module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.TriadicMeanComparison

@[expose] public section

/-!
# Theta ladder: finite triadic mean telescope

This file records the deterministic last step of the Campanato readout.  A
pointwise scale-zero endpoint is joined to the finite chain of centered
normalized-`L²` rows.  The estimate is deliberately stated for an arbitrary
representative, so the probabilistic theta ladder and the canonical
representative can be assembled without changing this argument.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

noncomputable section

variable {d : ℕ}

/-- Join a pointwise scale-zero endpoint to the finite concentric triadic
mean telescope. -/
theorem abs_point_sub_triadicMean_le_of_halfDecay
    {top : ℕ} {x : Vec d} {f fRep : Vec d → ℝ} {A E : ℝ}
    (hA : 0 ≤ A)
    (hf : IntegrableOn f (translatedCube d (top : ℤ) x))
    (hf2 : IntegrableOn (fun y ↦ f y ^ 2)
      (translatedCube d (top : ℤ) x))
    (hdecay : ∀ s : ℕ, s ≤ top →
      normalizedL2On (translatedCube d (s : ℤ) x)
          (fun y ↦ f y - averageOn (translatedCube d (s : ℤ) x) f) ≤
        A * (3 : ℝ) ^
          (-(1 / 2 : ℝ) * ((top : ℝ) - (s : ℝ))))
    (hpoint : |fRep x - averageOn (translatedCube d 0 x) f| ≤ E) :
    |fRep x - averageOn (translatedCube d (top : ℤ) x) f| ≤
      E + 5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * A := by
  have hmean := abs_averageOn_translatedCube_nat_sub_le_of_halfDecay
    (d := d) (top := top) (n := 0) (Nat.zero_le top) hA hf hf2
    (fun s _hs0 hstop ↦ hdecay s hstop)
  have htri := abs_sub_le (fRep x)
    (averageOn (translatedCube d 0 x) f)
    (averageOn (translatedCube d (top : ℤ) x) f)
  exact htri.trans (add_le_add hpoint hmean)

/-- A common-reference point bound gives the literal oscillation bound.  The
explicit boundedness proof is important because `oscillationOn` is an
`sSup`. -/
theorem oscillationOn_le_two_mul_of_point_sub_common
    {S : Set (Vec d)} {f : Vec d → ℝ} {a K : ℝ}
    (hS : S.Nonempty)
    (hpoint : ∀ x ∈ S, |f x - a| ≤ K) :
    oscillationOn S f ≤ 2 * K := by
  unfold oscillationOn
  apply csSup_le
  · obtain ⟨x, hx⟩ := hS
    exact ⟨0, x, hx, x, hx, by simp⟩
  · intro q hq
    rcases hq with ⟨x, hx, y, hy, rfl⟩
    have htri := abs_sub_le (f x) a (f y)
    have hy' : |a - f y| ≤ K := by
      simpa only [abs_sub_comm] using hpoint y hy
    exact htri.trans (by linarith [hpoint x hx, hy'])

/-- The same pointwise estimate, read as the undecayed supremum carrier used
by the bounded-multiplier conclusion. -/
theorem sSup_point_sub_common_le
    {S : Set (Vec d)} {f : Vec d → ℝ} {a K : ℝ}
    (hS : S.Nonempty)
    (hpoint : ∀ x ∈ S, |f x - a| ≤ K) :
    sSup {r : ℝ | ∃ x ∈ S, r = |f x - a|} ≤ K := by
  apply csSup_le
  · obtain ⟨x, hx⟩ := hS
    exact ⟨|f x - a|, x, hx, rfl⟩
  · intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    exact hpoint x hx

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
