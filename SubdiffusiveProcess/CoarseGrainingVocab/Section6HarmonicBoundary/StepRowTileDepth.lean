module

public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

/-!
# The tile depth of the boundary residual-mean row

The boundary tile family
(`WindowSummationBoundaryCellPrice.exists_windowSummation_projectedBoundaryCellPrice`)
prices the residual mean on a projected parent of scale `k` at any tile depth
`j`, with an energy coefficient

```text
Cface · 3^{(s/4)(n+2−κ)} · σ⁻¹ · (3^κ)² · 3^j ,       κ = k − j .
```

Multiplied by the row's normaliser `σ 3^{−2k}` this is

```text
Cface · 3^{(s/4)(n+2−k)} · 3^{(s/4−1) j} ,
```

so the row's *fixed* feedback constant `θ` is reached by choosing `j` large
enough, at the cost of the tile count `3^j` in the oscillation leg.

The crude choice `j ≥ (Δ+2)/15 + O(1)` is obtained from the
worst case `s = 1/4`.  That choice is **too big**: the parent-oscillation leg of
`StepRowBoundarySum.BoundaryStepCellParentRow` carries the loss factor
`3^{2s(n+2−k)}`, which degenerates to `1` as `s ↓ 512 M.delta²`, whereas
`3^{(Δ+2)/15}` does not.  The correct choice is `s`-adapted,

```text
j = ⌈(16/15)((s/4)(n+2−k) + A)⌉ ,     A = max 0 (log₃ (Cface/θ)) ,
```

for which `3^j ≤ K · 3^{2s(n+2−k)}` with `K = 3^{(16/15)A+1}` dimension-only,
because `(16/15)(s/4) = 4s/15 ≤ 2s`.  Both inequalities are proved below in one
statement, uniformly in `s ∈ (0, 1/4]` and in the depth `D = n+2−k ≥ 0`.

The tile depth is a free parameter.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

noncomputable section

/-- The dimension-free tile-count constant attached to a feedback target
`theta` and a face constant `Cface`. -/
def stepRowTileDepthConst (Cface theta : ℝ) : ℝ :=
  (3 : ℝ) ^ ((16 / 15 : ℝ) * max 0 (Real.logb 3 (Cface / theta)) + 1)

theorem stepRowTileDepthConst_pos (Cface theta : ℝ) :
    0 < stepRowTileDepthConst Cface theta :=
  Real.rpow_pos_of_pos (by norm_num) _

/- The superseded `exists_stepRowTileDepth`
was removed here.  Its exponent bookkeeping omitted the ASD prefactor; the
corrected statement is `exists_stepRowTileDepth_ofExponent` below, which is
what the boundary assembly uses.   -/


/-- **The tile depth against a prescribed loss exponent.**

The generalisation of `exists_stepRowTileDepth` that the boundary assembly
needs: the loss to be beaten is an arbitrary `3^E` rather than the tile family's
own `3^{(s/4)D}`, and the tile count is then bounded by `3^{(16/15)E}` — the
sharp constant, since `1 - s/4 ≥ 15/16` on `s ≤ 1/4`.

The exponent `E` that the boundary row must beat is
**not** `(s/4)(n+2-k)` but `(s/4)(n+2-k)` *plus the ASD prefactor's own*
`(7/4)s(n+2-k)`, i.e. `E = 2 s (n+2-k)`. The prefactor contributes the second summand. -/
theorem exists_stepRowTileDepth_ofExponent {Cface theta : ℝ} (hC : 0 < Cface)
    (htheta : 0 < theta) {s : ℝ} (hs4 : s ≤ 1 / 4)
    {E : ℝ} (hE : 0 ≤ E) :
    ∃ j : ℕ,
      Cface * (3 : ℝ) ^ E * (3 : ℝ) ^ ((s / 4 - 1) * (j : ℝ)) ≤ theta ∧
        (3 : ℝ) ^ ((j : ℕ) : ℝ) ≤ stepRowTileDepthConst Cface theta *
          (3 : ℝ) ^ ((16 / 15 : ℝ) * E) := by
  have h3 : (1 : ℝ) < 3 := by norm_num
  set A : ℝ := max 0 (Real.logb 3 (Cface / theta)) with hA
  have hA0 : 0 ≤ A := le_max_left _ _
  have hAlog : Real.logb 3 (Cface / theta) ≤ A := le_max_right _ _
  set B : ℝ := (16 / 15 : ℝ) * (E + A) with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  refine ⟨⌈B⌉₊, ?_, ?_⟩
  · have hjge : B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil _
    have hcoef : (1 : ℝ) - s / 4 ≥ 15 / 16 := by linarith only [hs4]
    have hkey : E + A ≤ (1 - s / 4) * (⌈B⌉₊ : ℝ) := by
      have h1 : (15 / 16 : ℝ) * (⌈B⌉₊ : ℝ) ≤ (1 - s / 4) * (⌈B⌉₊ : ℝ) := by
        have : (0 : ℝ) ≤ (⌈B⌉₊ : ℝ) := Nat.cast_nonneg _
        nlinarith only [hcoef, this]
      have h2 : E + A ≤ (15 / 16 : ℝ) * (⌈B⌉₊ : ℝ) := by
        have : (15 / 16 : ℝ) * B = E + A := by rw [hB]; ring
        nlinarith only [hjge, this]
      linarith only [h1, h2]
    have hexp : E + (s / 4 - 1) * (⌈B⌉₊ : ℝ) ≤ -A := by
      have : (s / 4 - 1) * (⌈B⌉₊ : ℝ) = -((1 - s / 4) * (⌈B⌉₊ : ℝ)) := by ring
      rw [this]
      linarith only [hkey]
    have hmul : (3 : ℝ) ^ E * (3 : ℝ) ^ ((s / 4 - 1) * (⌈B⌉₊ : ℝ)) =
        (3 : ℝ) ^ (E + (s / 4 - 1) * (⌈B⌉₊ : ℝ)) :=
      (Real.rpow_add (by norm_num) _ _).symm
    have hle : (3 : ℝ) ^ (E + (s / 4 - 1) * (⌈B⌉₊ : ℝ)) ≤ (3 : ℝ) ^ (-A) :=
      Real.rpow_le_rpow_of_exponent_le h3.le hexp
    have hratio : (3 : ℝ) ^ (-A) ≤ theta / Cface := by
      have hpos : 0 < Cface / theta := div_pos hC htheta
      have hmono : (3 : ℝ) ^ (-A) ≤
          (3 : ℝ) ^ (-Real.logb 3 (Cface / theta)) :=
        Real.rpow_le_rpow_of_exponent_le h3.le (by linarith only [hAlog])
      have heq : (3 : ℝ) ^ (-Real.logb 3 (Cface / theta)) =
          (Cface / theta)⁻¹ := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_logb (by norm_num)
          (by norm_num) hpos]
      rw [heq] at hmono
      rwa [inv_div] at hmono
    calc Cface * (3 : ℝ) ^ E * (3 : ℝ) ^ ((s / 4 - 1) * (⌈B⌉₊ : ℝ))
        = Cface * ((3 : ℝ) ^ E * (3 : ℝ) ^ ((s / 4 - 1) * (⌈B⌉₊ : ℝ))) := by ring
      _ ≤ Cface * (theta / Cface) :=
          mul_le_mul_of_nonneg_left (by rw [hmul]; exact hle.trans hratio) hC.le
      _ = theta := by field_simp
  · have hjle : (⌈B⌉₊ : ℝ) ≤ B + 1 := (Nat.ceil_lt_add_one hB0).le
    have hexp : ((⌈B⌉₊ : ℕ) : ℝ) ≤ (16 / 15 : ℝ) * E +
        ((16 / 15 : ℝ) * A + 1) := by
      have hsplit : B + 1 = (16 / 15 : ℝ) * E + ((16 / 15 : ℝ) * A + 1) := by
        rw [hB]; ring
      linarith only [hjle, hsplit.le, hsplit.ge]
    calc (3 : ℝ) ^ ((⌈B⌉₊ : ℕ) : ℝ)
        ≤ (3 : ℝ) ^ ((16 / 15 : ℝ) * E + ((16 / 15 : ℝ) * A + 1)) :=
          Real.rpow_le_rpow_of_exponent_le h3.le hexp
      _ = stepRowTileDepthConst Cface theta * (3 : ℝ) ^ ((16 / 15 : ℝ) * E) := by
          rw [stepRowTileDepthConst, hA, Real.rpow_add (by norm_num)]
          ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
