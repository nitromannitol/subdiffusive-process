module

public import SubdiffusiveProcess.Paper.in_deterministic

@[expose] public section

/-! A finite same-cutoff drift prefix controls each included physical layer.
The score is the pinned primitive score, and its finiteness guard is explicit. -/
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators ENNReal
noncomputable section
namespace Paper

/-- The root layer is controlled by its literal finite drift-prefix sum. -/
theorem goodext_prefix_layer_bound
    {d : ℕ} [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (xi : BilateralField d) (N : ℕ) (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = xi ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (s eps : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (z : SpatialCoordinates d) (l : ℤ) (hlN : l < (N : ℤ)) (cbuf D : ℕ)
    (hfin : Dsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • z) ≠ ⊤)
    (B : ℝ)
    (hprefix : (∑ j ∈ Finset.Icc (l - (cbuf : ℤ)) (l + (D : ℤ)),
      if 0 ≤ (N : ℤ) - j then
        (Dsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • z)).toReal else 0) ≤ B) :
    |xi (-l) z| ≤ 2 * B := by
  have hLayer := aux_in_deterministic_onestep_omega_le_draw
    M xi N eta hEta s eps hs Fsc Psc Rsc Dsc Zsc goodEvt hPS z l hlN hfin
  have hlmem : l ∈ Finset.Icc (l - (cbuf : ℤ)) (l + (D : ℤ)) := by
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hsum : (Dsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • z)).toReal ≤
      ∑ j ∈ Finset.Icc (l - (cbuf : ℤ)) (l + (D : ℤ)),
        if 0 ≤ (N : ℤ) - j then
          (Dsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • z)).toReal else 0 := by
    have h := Finset.single_le_sum
      (f := fun j : ℤ => if 0 ≤ (N : ℤ) - j then
        (Dsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • z)).toReal else 0)
      (fun j _ => by split_ifs <;> positivity) hlmem
    simpa only [if_pos (show 0 ≤ (N : ℤ) - l by omega)] using h
  exact hLayer.trans (mul_le_mul_of_nonneg_left (hsum.trans hprefix) (by norm_num))

end Paper
