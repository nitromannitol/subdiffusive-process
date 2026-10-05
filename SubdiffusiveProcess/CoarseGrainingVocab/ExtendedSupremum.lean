module

public import Mathlib.Basic.ENNReal.Operations

@[expose] public section

/-! Finite real readouts of extended suprema. The boundedness hypotheses
justify conversion; the extended definitions themselves retain infinity. -/

open Set
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab

/-- A bounded real family has finite extended nonnegative supremum. -/
theorem sup_ofReal_ne_top {S : Set ℝ} (hS : BddAbove S) :
    sSup (ENNReal.ofReal '' S) ≠ ∞ := by
  obtain ⟨b, hb⟩ := hS
  have hle : sSup (ENNReal.ofReal '' S) ≤ ENNReal.ofReal b := by
    apply sSup_le
    rintro r ⟨r', hr', rfl⟩
    exact ENNReal.ofReal_le_ofReal (hb hr')
  exact ne_of_lt (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)

/-- On a nonempty bounded family, extending the supremum preserves its value. -/
theorem extended_sup_eq_of_bddAbove {S : Set ℝ} (hS : S.Nonempty)
    (hb : BddAbove S) : sSup (ENNReal.ofReal '' S) = ENNReal.ofReal (sSup S) := by
  have hle : sSup (ENNReal.ofReal '' S) ≤ ENNReal.ofReal (sSup S) := by
    apply sSup_le
    rintro _ ⟨a, ha, rfl⟩
    exact ENNReal.ofReal_le_ofReal (le_csSup hb ha)
  have hne : sSup (ENNReal.ofReal '' S) ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)
  refine le_antisymm hle ?_
  apply ENNReal.ofReal_le_of_le_toReal
  apply csSup_le hS
  intro a ha
  exact (ENNReal.ofReal_le_iff_le_toReal hne).mp (le_sSup ⟨a, ha, rfl⟩)

/-- The totalized real readout identity alone makes no finiteness assertion. -/
theorem extended_sup_toReal {S : Set ℝ} (hn : ∀ r ∈ S, 0 ≤ r) :
    (sSup (ENNReal.ofReal '' S)).toReal = sSup S := by
  have hf : ∀ r ∈ ENNReal.ofReal '' S, r ≠ ∞ := by
    rintro _ ⟨r, hr, rfl⟩
    exact ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_sSup _ hf]
  have himg : ENNReal.toReal '' (ENNReal.ofReal '' S) = S := by
    ext x
    constructor
    · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      rw [ENNReal.toReal_ofReal (hn r hr)]
      exact hr
    · intro hx
      exact ⟨ENNReal.ofReal x, ⟨x, hx, rfl⟩, ENNReal.toReal_ofReal (hn x hx)⟩
  rw [himg]

/-- Both components must be finite before distributing the real readout over their sum. -/
theorem full_norm_real_eq {S V : Set ℝ} {a : ℝ}
    (hS : BddAbove S) (hV : BddAbove V)
    (hS0 : ∀ r ∈ S, 0 ≤ r) (hV0 : ∀ r ∈ V, 0 ≤ r) (ha : 0 ≤ a) :
    (sSup (ENNReal.ofReal '' S) + ENNReal.ofReal a *
      sSup (ENNReal.ofReal '' V)).toReal = sSup S + a * sSup V := by
  have h1 := sup_ofReal_ne_top hS
  have h2 := sup_ofReal_ne_top hV
  rw [ENNReal.toReal_add h1 (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h2),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal ha,
    extended_sup_toReal hS0, extended_sup_toReal hV0]

end SubdiffusiveProcess.CoarseGrainingVocab
