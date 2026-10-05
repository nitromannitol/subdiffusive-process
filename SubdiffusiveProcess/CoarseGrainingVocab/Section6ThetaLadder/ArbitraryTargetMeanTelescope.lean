module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.TriadicMeanTelescope

@[expose] public section

/-!
# Theta ladder: arbitrary-target parent-mean telescope

The undecayed readout does not need the target to be a triadic cube.  Each
point is joined to its scale-zero mean, telescoped concentrically to the
comparison scale, and then compared with the parent mean.  This formulation
is the shallow-depth companion to the target-cube oscillation readout.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- The finite point-to-parent-mean telescope, uniformly over an arbitrary
nonempty target set. -/
theorem sSup_point_sub_parentMean_le_of_halfDecay
    {top : ℕ} {S : Set (Vec d)} (hS : S.Nonempty)
    {f fRep : Vec d → ℝ} {A P0 T Pparent : ℝ}
    (hA : 0 ≤ A) (hP0 : 0 ≤ P0)
    (hInt : ∀ x ∈ S,
      IntegrableOn f (translatedCube d (top : ℤ) x) ∧
      IntegrableOn (fun y ↦ f y ^ 2) (translatedCube d (top : ℤ) x))
    (hrows : ∀ x ∈ S, ∀ s : ℕ, s ≤ top →
      normalizedL2On (translatedCube d (s : ℤ) x)
          (fun y ↦ f y - averageOn (translatedCube d (s : ℤ) x) f) ≤
        A * (3 : ℝ) ^
          (-(1 / 2 : ℝ) * ((top : ℝ) - (s : ℝ))))
    (hpoint0 : ∀ x ∈ S,
      |fRep x - averageOn (translatedCube d 0 x) f| ≤
        P0 * normalizedL2On (translatedCube d 0 x)
          (fun y ↦ f y - averageOn (translatedCube d 0 x) f))
    (htopMean : ∀ x ∈ S,
      |averageOn (translatedCube d (top : ℤ) x) f - Pparent| ≤ T) :
    sSup {r : ℝ | ∃ x ∈ S, r = |fRep x - Pparent|} ≤
      P0 * (A * (3 : ℝ) ^ (-(1 / 2 : ℝ) * (top : ℝ))) +
        5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * A + T := by
  let E := P0 * (A * (3 : ℝ) ^ (-(1 / 2 : ℝ) * (top : ℝ)))
  have hpoint : ∀ x ∈ S,
      |fRep x - averageOn (translatedCube d (top : ℤ) x) f| ≤
        E + 5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * A := by
    intro x hx
    have hzero := hrows x hx 0 (Nat.zero_le top)
    have hzeroScaled := mul_le_mul_of_nonneg_left hzero hP0
    have hbase : |fRep x - averageOn (translatedCube d 0 x) f| ≤ E :=
      (hpoint0 x hx).trans (by
        simpa only [E, Nat.cast_zero, sub_zero] using hzeroScaled)
    exact abs_point_sub_triadicMean_le_of_halfDecay hA
      (hInt x hx).1 (hInt x hx).2 (hrows x hx) hbase
  apply sSup_point_sub_common_le hS
  intro x hx
  have htri := abs_sub_le (fRep x)
    (averageOn (translatedCube d (top : ℤ) x) f) Pparent
  exact htri.trans (by
    simpa only [E, add_assoc] using add_le_add (hpoint x hx) (htopMean x hx))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
