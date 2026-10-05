module

public import SubdiffusiveProcess.ResponseMoments.Interfaces
public import SubdiffusiveProcess.ResponseMoments.Forms
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Fine step of `mfd:lem-shifts`: the one-dimensional count of grid points
near the integers, which is the only quantitative content of the residue
geometry.

`t + r/M` for `r < M` are the shifted positions of one coordinate; the claim
is that at most `2(delta M + 1)` of them lie within `delta` of an integer.
For `delta >= 1/2` this is trivial, since all `M` residues qualify and
`M <= 2 delta M`; for `delta < 1/2` the near-integer set meets a period in at
most two intervals of total length `2 delta`, each containing at most
`length * M + 1` of the equally spaced points. -/
theorem grid_points_near_integers (Mm : ℕ) (hM : 0 < Mm) (t delta : ℝ)
    (hdelta : 0 ≤ delta) (bad : Finset (Fin Mm))
    (hmem : ∀ r : Fin Mm, r ∈ bad ↔
      ∃ k : ℤ, |t + ((r : ℕ) : ℝ) / (Mm : ℝ) - (k : ℝ)| ≤ delta) :
    ((bad.card : ℝ)) ≤ 2 * (delta * (Mm : ℝ) + 1) := by
  classical
  have hMR : (0:ℝ) < (Mm : ℝ) := by exact_mod_cast hM
  have hex : ∀ r : Fin Mm, ∃ k : ℤ, r ∈ bad →
      |t + ((r : ℕ) : ℝ) / (Mm : ℝ) - (k : ℝ)| ≤ delta := by
    intro r
    by_cases h : r ∈ bad
    · obtain ⟨k, hk⟩ := (hmem r).mp h
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun hc => absurd hc h⟩
  choose kf hkf using hex
  set A : ℤ := ⌈-((Mm : ℝ) * t) - delta * (Mm : ℝ)⌉ with hA
  set B : ℤ := ⌊-((Mm : ℝ) * t) + delta * (Mm : ℝ)⌋ with hB
  set f : Fin Mm → ℤ := fun r => (r : ℕ) - (Mm : ℤ) * kf r with hf
  have hmaps : ∀ r ∈ bad, f r ∈ Finset.Icc A B := by
    intro r hr
    have hk := hkf r hr
    rw [abs_le] at hk
    obtain ⟨h1, h2⟩ := hk
    have e1 : ((f r : ℤ) : ℝ) = ((r : ℕ) : ℝ) - (Mm : ℝ) * ((kf r : ℤ) : ℝ) := by
      simp [hf]
    have hmul1 : -(delta * (Mm : ℝ)) ≤
        ((r : ℕ) : ℝ) - (Mm : ℝ) * ((kf r : ℤ) : ℝ) + (Mm : ℝ) * t := by
      have := mul_le_mul_of_nonneg_left h1 (le_of_lt hMR)
      have hexp : (Mm : ℝ) * (t + ((r : ℕ) : ℝ) / (Mm : ℝ) - ((kf r : ℤ) : ℝ)) =
          ((r : ℕ) : ℝ) - (Mm : ℝ) * ((kf r : ℤ) : ℝ) + (Mm : ℝ) * t := by
        field_simp; ring
      rw [hexp] at this
      nlinarith [this, hMR]
    have hmul2 : ((r : ℕ) : ℝ) - (Mm : ℝ) * ((kf r : ℤ) : ℝ) + (Mm : ℝ) * t ≤
        delta * (Mm : ℝ) := by
      have := mul_le_mul_of_nonneg_left h2 (le_of_lt hMR)
      have hexp : (Mm : ℝ) * (t + ((r : ℕ) : ℝ) / (Mm : ℝ) - ((kf r : ℤ) : ℝ)) =
          ((r : ℕ) : ℝ) - (Mm : ℝ) * ((kf r : ℤ) : ℝ) + (Mm : ℝ) * t := by
        field_simp; ring
      rw [hexp] at this
      nlinarith [this, hMR]
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · rw [hA]
      refine Int.ceil_le.mpr ?_
      rw [e1]
      linarith [hmul1]
    · rw [hB]
      refine Int.le_floor.mpr ?_
      rw [e1]
      linarith [hmul2]
  have hinj : Set.InjOn f bad := by
    intro r hr r' hr' hEq
    have h1 : ((r : ℕ) : ℤ) - (Mm : ℤ) * kf r = ((r' : ℕ) : ℤ) - (Mm : ℤ) * kf r' :=
      hEq
    have hdiff : ((r : ℕ) : ℤ) - ((r' : ℕ) : ℤ) =
        (Mm : ℤ) * (kf r - kf r') := by linarith [h1]
    have hlt : ((r : ℕ) : ℤ) < (Mm : ℤ) := by exact_mod_cast r.isLt
    have hlt' : ((r' : ℕ) : ℤ) < (Mm : ℤ) := by exact_mod_cast r'.isLt
    have hnn : (0 : ℤ) ≤ ((r : ℕ) : ℤ) := Int.natCast_nonneg _
    have hnn' : (0 : ℤ) ≤ ((r' : ℕ) : ℤ) := Int.natCast_nonneg _
    have hk : kf r = kf r' := by
      by_contra hne
      have hge : 1 ≤ |kf r - kf r'| :=
        Int.one_le_abs (sub_ne_zero.mpr hne)
      have habs : |((r : ℕ) : ℤ) - ((r' : ℕ) : ℤ)| < (Mm : ℤ) := by
        rw [abs_lt]; omega
      rw [hdiff, abs_mul] at habs
      have hMabs : |(Mm : ℤ)| = (Mm : ℤ) := abs_of_nonneg (Int.natCast_nonneg _)
      rw [hMabs] at habs
      nlinarith [habs, hge, (by exact_mod_cast hM : (0:ℤ) < (Mm : ℤ))]
    rw [hk] at hdiff
    have hval : ((r : ℕ) : ℤ) = ((r' : ℕ) : ℤ) := by omega
    have hnat : (r : ℕ) = (r' : ℕ) := by exact_mod_cast hval
    exact Fin.ext hnat
  have hcard : bad.card ≤ (Finset.Icc A B).card :=
    Finset.card_le_card_of_injOn f hmaps hinj
  have hIcc : ((Finset.Icc A B).card : ℝ) ≤ 2 * (delta * (Mm : ℝ) + 1) := by
    rw [Int.card_Icc]
    have hBA : (B : ℝ) - (A : ℝ) ≤ 2 * (delta * (Mm : ℝ)) := by
      have hb : (B : ℝ) ≤ -((Mm : ℝ) * t) + delta * (Mm : ℝ) := Int.floor_le _
      have ha : -((Mm : ℝ) * t) - delta * (Mm : ℝ) ≤ (A : ℝ) := Int.le_ceil _
      linarith
    rcases le_or_gt (B + 1 - A) 0 with h | h
    · rw [Int.toNat_of_nonpos h]
      push_cast
      nlinarith [hdelta, hMR]
    · have hz : (((B + 1 - A).toNat : ℕ) : ℤ) = B + 1 - A :=
        Int.toNat_of_nonneg (by omega)
      have hcast : (((B + 1 - A).toNat : ℕ) : ℝ) = (B : ℝ) - (A : ℝ) + 1 := by
        have h2 := congrArg (fun z : ℤ => (z : ℝ)) hz
        push_cast at h2
        linarith [h2]
      rw [hcast]
      linarith [hBA]
  calc ((bad.card : ℝ)) ≤ ((Finset.Icc A B).card : ℝ) := by exact_mod_cast hcard
    _ ≤ 2 * (delta * (Mm : ℝ) + 1) := hIcc

end SubdiffusiveProcess.Paper
