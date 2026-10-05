module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic

@[expose] public section

/-! Pointwise Holder bounds supply the bounded quotient set and its seminorm bound.
No regularity or representative existence is asserted. -/
open Set _root_.SubdiffusiveProcess.EllipticRegularity
open scoped BigOperators
namespace SubdiffusiveProcess

/-- A uniform pair bound proves Holder membership and bounds its actual seminorm. -/
theorem isHolderOn_and_seminorm_le_of_pairs {d : ℕ} (alpha A : ℝ) (hA : 0 ≤ A)
    (S : Set (SpatialCoordinates d)) (U : SpatialCoordinates d → ℝ)
    (hpair : ∀ x ∈ S,∀ y ∈ S,
      |U x-U y| ≤ A*(Real.sqrt (∑ i : Fin d,(x i-y i)^2))^alpha) :
    IsHolderOn alpha S U ∧ holderSeminorm alpha S U ≤ A := by
  have hbound : ∀ v ∈ holderRatioSet alpha S U,v ≤ A := by
    rintro v ⟨x,hx,y,hy,hxy,rfl⟩
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hxy
    have hs : 0 < ∑ j : Fin d,(x j-y j)^2 := lt_of_lt_of_le
      (sq_pos_of_ne_zero (sub_ne_zero.mpr hi))
      (Finset.single_le_sum (fun j _ => sq_nonneg (x j-y j)) (Finset.mem_univ i))
    have hp := Real.rpow_pos_of_pos (Real.sqrt_pos.mpr hs) alpha
    exact (div_le_iff₀ hp).mpr (hpair x hx y hy)
  exact ⟨⟨A,hbound⟩,Real.sSup_le hbound hA⟩

end SubdiffusiveProcess
