module

public import SubdiffusiveProcess.ResponseMoments.Forms
public import Mathlib.Tactic

@[expose] public section

/-!
# Strict improvement of an endpoint, and proportionality

paper label `mfd:thm-prop`, Theorem `mfd:thm-prop`
`strict_endpoint_improvement` is the passage from the
summed affine saving to the improved upper endpoint (paper label `mfd:thm-prop`);
`proportionality` is the contradiction with optimality of the endpoints that
gives `Δ = 0` and `F = m E` (paper label `mfd:thm-prop`).
-/

noncomputable section

namespace SubdiffusiveProcess
namespace ResponseMoments

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {X : Type*} [MeasurableSpace X]

/-- Strict improvement of the upper endpoint.
`hsave` is the summed affine saving of  together with the
harmonic-replacement competitor, and its second clause is the lower
semicontinuity of `F` along that competitor. -/
theorem strict_endpoint_improvement (E F : LocalEnergy V X) (m M k1 : ℝ)
    (_hmM : m < M) (_hk1 : 0 < k1)
    (hsave : ∀ (u : V) (eps : ℝ), 0 < eps → ∃ v : V,
      F.form v v ≤ M * E.form u u - k1 * (M - m) * E.form u u + eps ∧
        F.form u u ≤ F.form v v + eps) :
    ∀ u : V, F.form u u ≤ (M - k1 * (M - m)) * E.form u u := by
  intro u
  refine le_of_forall_pos_le_add ?_
  intro eps heps
  obtain ⟨v, h1, h2⟩ := hsave u (eps / 2) (by linarith)
  have hring : (M - k1 * (M - m)) * E.form u u =
      M * E.form u u - k1 * (M - m) * E.form u u := by ring
  linarith

/-- Proportionality, paper `mfd:thm-prop`, : the gap vanishes
and the two candidates are proportional with the deterministic constant `m`. -/
theorem proportionality (E F : LocalEnergy V X) (m M k1 : ℝ)
    (_hmpos : 0 < m) (hmM : m ≤ M) (hk1 : 0 < k1)
    (hmE : ∀ u : V, m * E.form u u ≤ F.form u u)
    (hME : ∀ u : V, F.form u u ≤ M * E.form u u)
    (hMinf : ∀ b : ℝ, (∀ u : V, F.form u u ≤ b * E.form u u) → M ≤ b)
    (hmsup : ∀ b : ℝ, (∀ u : V, b * E.form u u ≤ F.form u u) → b ≤ m)
    (himp : m < M →
      ((∀ u : V, F.form u u ≤ (M - k1 * (M - m)) * E.form u u) ∨
        (∀ u : V, (m + k1 * (M - m)) * E.form u u ≤ F.form u u))) :
    M = m ∧ ∀ u : V, F.form u u = m * E.form u u := by
  have hMm : M = m := by
    by_contra hne
    have hlt : m < M := lt_of_le_of_ne hmM (Ne.symm hne)
    rcases himp hlt with h | h
    · have hle := hMinf _ h
      nlinarith
    · have hle := hmsup _ h
      nlinarith
  refine ⟨hMm, fun u => ?_⟩
  have h1 := hmE u
  have h2 := hME u
  rw [hMm] at h2
  linarith

end ResponseMoments
end SubdiffusiveProcess
