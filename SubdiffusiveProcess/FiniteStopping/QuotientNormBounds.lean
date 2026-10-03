module

public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.CoefficientRestriction
public import SubdiffusiveProcess.Lane3.Subdivision
public import SubdiffusiveProcess.Lane3.Interfaces
public import SubdiffusiveProcess.Geometry.OddGrid
public import SubdiffusiveProcess.Lane2.CellDirichlet
public import SubdiffusiveProcess.Lane2.BoundaryResponse
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.Lane4.Inputs
public import Mathlib.Analysis.Seminorm
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJDeterministic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
public import SubdiffusiveProcess.Assumptions.Actions
public import SubdiffusiveProcess.Main.LayerScaling
public import Mathlib.Tactic

@[expose] public section

/-! This module establishes forall c to quotient for finite stopping; it does not assert the full stopping theorem. -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.FiniteStopping

variable {d : ℕ}

/-- cancel pos left in the finite stopping construction. -/
theorem cancel_pos_left (X Y A : ℝ) (hA : 0 < A) (hXY : A * X ≤ A * Y) : X ≤ Y := by
  have hAinv : 0 ≤ A⁻¹ := (inv_pos.mpr hA).le
  have h := mul_le_mul_of_nonneg_left hXY hAinv
  rwa [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hA.ne', one_mul, one_mul] at h

/-- forall c to quotient in the finite stopping construction. -/
theorem forall_c_to_quotient {d : ℕ} (beta : ℝ) (S : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) (X K : ℝ) (hX : 0 ≤ X) (hK : 0 < K)
    (h : ∀ c : ℝ, X ≤ K * (cAlphaNorm beta S (fun x => f x - c)) ^ 2) :
    X ≤ K * (quotientCBetaNorm beta S f) ^ 2 := by
  have hcA_nonneg : ∀ c : ℝ, 0 ≤ cAlphaNorm beta S (fun x => f x - c) := by
    intro c
    unfold cAlphaNorm
    have h1 : 0 ≤ sSup {v : ℝ | ∃ x ∈ S, v = |f x - c|} := by
      rcases Set.eq_empty_or_nonempty {v : ℝ | ∃ x ∈ S, v = |f x - c|} with he | hne
      · simp only [he, Real.sSup_empty, le_refl]
      · obtain ⟨v0, x0, hx0, rfl⟩ := hne
        by_cases hbdd : BddAbove {v : ℝ | ∃ x ∈ S, v = |f x - c|}
        · exact le_trans (abs_nonneg _) (le_csSup hbdd ⟨x0, hx0, rfl⟩)
        · simp only [Real.sSup_of_not_bddAbove hbdd, le_refl]
    have h2 : 0 ≤ holderSeminorm beta S (fun x => f x - c) := by
      unfold holderSeminorm
      rcases Set.eq_empty_or_nonempty (holderRatioSet beta S (fun x => f x - c)) with he | hne
      · simp only [he, Real.sSup_empty, le_refl]
      · obtain ⟨v0, x0, hx0, y0, hy0, hxy0, rfl⟩ := hne
        by_cases hbdd : BddAbove (holderRatioSet beta S (fun x => f x - c))
        · exact le_trans (div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _))
            (le_csSup hbdd ⟨x0, hx0, y0, hy0, hxy0, rfl⟩)
        · simp only [Real.sSup_of_not_bddAbove hbdd, le_refl]
    linarith only [hX, hK, h, h1, h2]
  have hsqrt : ∀ c : ℝ, Real.sqrt (X / K) ≤ cAlphaNorm beta S (fun x => f x - c) := by
    intro c
    have h1 : X / K ≤ (cAlphaNorm beta S (fun x => f x - c)) ^ 2 := by
      rw [div_le_iff₀ hK]
      have := h c
      linarith only [hX, hK, h, hcA_nonneg, this]
    calc Real.sqrt (X / K) ≤ Real.sqrt ((cAlphaNorm beta S (fun x => f x - c)) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = cAlphaNorm beta S (fun x => f x - c) := Real.sqrt_sq (hcA_nonneg c)
  have hXK0 : 0 ≤ X / K := div_nonneg hX hK.le
  have hle : Real.sqrt (X / K) ≤ quotientCBetaNorm beta S f := by
    apply le_csInf
    · exact ⟨cAlphaNorm beta S (fun x => f x - 0), 0, rfl⟩
    · rintro v ⟨c, rfl⟩
      exact hsqrt c
  have hsq : (Real.sqrt (X / K)) ^ 2 ≤ (quotientCBetaNorm beta S f) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
  rw [Real.sq_sqrt hXK0] at hsq
  calc X = K * (X / K) := by field_simp
    _ ≤ K * (quotientCBetaNorm beta S f) ^ 2 := mul_le_mul_of_nonneg_left hsq hK.le

end SubdiffusiveProcess.FiniteStopping
