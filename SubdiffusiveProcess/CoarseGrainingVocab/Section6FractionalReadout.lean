module

public import SubdiffusiveProcess.CoarseGrainingVocab.ExtendedSupremum
public import SubdiffusiveProcess.Frozen.Section6.Defs.FractionalInfinityNormOn

@[expose] public section

/-! Real arithmetic readout of the extended fractional norm. Finite equality
with the component suprema is proved under boundedness of both sets of values.
The Section 6 theorem consumers supply MemHolder on a bounded cube. -/
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab

/-- Real readout for the existing finite Holder estimates. -/
def fractionalInfinityNormOnReal {d : ℕ} (W : Set (Vec d)) (ell s : ℝ)
    (f : Vec d → Vec d) (_hell : 0 < ell := by positivity) : ℝ :=
  (fractionalInfinityNormOn W ell s f _hell).toReal

/-- Finiteness requires bounded difference quotients and bounded values. -/
theorem fractionalInfinityNormOn_ne_top_of_bddAbove {d : ℕ} {W : Set (Vec d)}
    {ell s : ℝ} {f : Vec d → Vec d} (hell : 0 < ell)
    (hsemi : BddAbove {r : ℝ | ∃ x ∈ W, ∃ y ∈ W, x ≠ y ∧
      r = Homogenization.euclideanNorm (f x - f y) /
        Homogenization.euclideanNorm (x - y) ^ s})
    (hvalues : BddAbove {r : ℝ | ∃ x ∈ W,
      r = Homogenization.euclideanNorm (f x)}) :
    fractionalInfinityNormOn W ell s f hell ≠ ∞ := by
  exact ENNReal.add_ne_top.mpr ⟨sup_ofReal_ne_top hsemi,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (sup_ofReal_ne_top hvalues)⟩

/-- On the finite carrier, the extended full norm has the original real formula. -/
theorem fractionalInfinityNormOnReal_eq_of_bddAbove {d : ℕ} {W : Set (Vec d)}
    {ell s : ℝ} {f : Vec d → Vec d} (hell : 0 < ell)
    (hsemi : BddAbove {r : ℝ | ∃ x ∈ W, ∃ y ∈ W, x ≠ y ∧
      r = Homogenization.euclideanNorm (f x - f y) /
        Homogenization.euclideanNorm (x - y) ^ s})
    (hvalues : BddAbove {r : ℝ | ∃ x ∈ W,
      r = Homogenization.euclideanNorm (f x)}) :
    fractionalInfinityNormOnReal W ell s f hell =
      holderSeminormOn W s f + ell ^ (-s) * vectorSupNormOn W f := by
  apply full_norm_real_eq hsemi hvalues
  · rintro r ⟨x, _hx, y, _hy, _hxy, rfl⟩
    exact div_nonneg (Homogenization.euclideanNorm_nonneg _)
      (Real.rpow_nonneg (Homogenization.euclideanNorm_nonneg _) _)
  · rintro r ⟨x, _hx, rfl⟩
    exact Homogenization.euclideanNorm_nonneg _
  · exact Real.rpow_nonneg hell.le _

/-- The zero-dimensional field has zero full norm, including on the empty window. -/
theorem full_norm_dim_zero (W : Set (Vec 0)) (ell s : ℝ)
    (f : Vec 0 → Vec 0) (hell : 0 < ell) :
    fractionalInfinityNormOnReal W ell s f hell = 0 := by
  have hxy : ∀ x y : Vec 0, x = y := by
    intro x y
    funext i
    exact Fin.elim0 i
  have hfx : ∀ x : Vec 0, f x = 0 := by
    intro x
    funext i
    exact Fin.elim0 i
  have hsem : fractionalInfinitySeminormOn W s f = 0 := by
    have hset : {r : ℝ | ∃ x ∈ W, ∃ y ∈ W, x ≠ y ∧
        r = Homogenization.euclideanNorm (f x - f y) /
          Homogenization.euclideanNorm (x - y) ^ s} = ∅ := by
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨x, _hx, y, _hy, hne, _hr⟩
      exact hne (hxy x y)
    unfold fractionalInfinitySeminormOn
    rw [hset, Set.image_empty, sSup_empty]
    rfl
  have hsup : sSup (ENNReal.ofReal '' {r : ℝ | ∃ x ∈ W,
      r = Homogenization.euclideanNorm (f x)}) = 0 := by
    refine le_antisymm (sSup_le ?_) bot_le
    rintro r ⟨v, ⟨x, _hxW, rfl⟩, rfl⟩
    rw [hfx x, Homogenization.euclideanNorm_zero, ENNReal.ofReal_zero]
  unfold fractionalInfinityNormOnReal fractionalInfinityNormOn
  rw [hsem, hsup, mul_zero, add_zero, ENNReal.toReal_zero]

end SubdiffusiveProcess.CoarseGrainingVocab
