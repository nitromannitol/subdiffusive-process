module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.EnergyRowScalar
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneFinal

@[expose] public section

/-!
# Frozen row 2: the conversion from the Step-6 budget

Interior Step 6 (`exists_interiorHolderProjectedEnergy_final`, unconditional)
bounds the local energy by the square root of a sum of two squares; the scalar
core `EnergyRowScalar.sqrt_projectedEnergyBudget_le` splits that into two
first-order legs,

```text
  √(81^d K) · ( √σ·3^{-n}·O  +  s^{-6}·σ^{-1/2}·3^{sn}·F ) ,
```

with `O` the parent oscillation and `F` the source seminorm.  Frozen row 2 is
reached once each leg is bounded by `gapTerm = 3^{(1-α)(m-n)}` times the
corresponding global quantity.  That last step is the conversion, proved here.

## The obstruction this makes explicit

Row 1 controls the oscillation **only at grid points** — its binder is
`∀ y, OnTriadicGrid ell y → y ∈ truncatedCube d m n x → …`.  Frozen row 2's base
point is an arbitrary `x ∈ cube d (m-1)`, with no grid binder at all.  So the
oscillation leg `hO` cannot be discharged from row 1 directly: it needs an
*off-grid transfer*, exactly as Step 7 needs one for the excess
(`Section6Holder.exists_holderOffGridExcessTransfer`).  Keeping `hO` as an
explicit hypothesis is what makes that requirement visible instead of hidden.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-- **The row-2 conversion.**  Two legs bounded by the frozen gap factor give
the frozen row-2 shape, under a single constant. -/
theorem interiorRowTwo_of_legs {d : ℕ}
    {K Elocal O F A B Eglobal Data gapTerm : ℝ}
    (hsplit : Elocal ≤ Real.sqrt ((81 : ℝ) ^ d * K) * (O + F))
    (hO : O ≤ A * gapTerm * Eglobal)
    (hF : F ≤ B * gapTerm * Data)
    (hgap0 : 0 ≤ gapTerm) (hEg : 0 ≤ Eglobal) (hData : 0 ≤ Data) :
    Elocal ≤ Real.sqrt ((81 : ℝ) ^ d * K) * max A B * gapTerm *
      (Eglobal + Data) := by
  have hroot : (0 : ℝ) ≤ Real.sqrt ((81 : ℝ) ^ d * K) := Real.sqrt_nonneg _
  have hA : A * gapTerm * Eglobal ≤ max A B * gapTerm * Eglobal := by
    have := mul_le_mul_of_nonneg_right (le_max_left A B) hgap0
    exact mul_le_mul_of_nonneg_right this hEg
  have hB : B * gapTerm * Data ≤ max A B * gapTerm * Data := by
    have := mul_le_mul_of_nonneg_right (le_max_right A B) hgap0
    exact mul_le_mul_of_nonneg_right this hData
  calc Elocal ≤ Real.sqrt ((81 : ℝ) ^ d * K) * (O + F) := hsplit
    _ ≤ Real.sqrt ((81 : ℝ) ^ d * K) *
        (max A B * gapTerm * Eglobal + max A B * gapTerm * Data) := by
        apply mul_le_mul_of_nonneg_left _ hroot
        exact add_le_add (hO.trans hA) (hF.trans hB)
    _ = Real.sqrt ((81 : ℝ) ^ d * K) * max A B * gapTerm *
        (Eglobal + Data) := by ring

/-- The conversion applied directly to the Step-6 square-root budget: the
scalar core supplies `hsplit`, and the two legs do the rest. -/
theorem interiorRowTwo_of_budget {d : ℕ}
    {K sigma s O F nr A B Eglobal Data gapTerm Elocal : ℝ} {n : ℤ}
    (hK : 0 ≤ K) (hsigma : 0 < sigma) (hs : 0 < s) (hO0 : 0 ≤ O) (hF0 : 0 ≤ F)
    (hbudget : Elocal ≤
      Real.sqrt ((81 : ℝ) ^ d *
        (K * (sigma * (3 : ℝ) ^ (-(2 * n)) * O ^ 2 +
          s ^ (-12 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ (2 * s * nr) * F ^ 2))))
    (hO : Real.sqrt sigma * (3 : ℝ) ^ (-n) * O ≤ A * gapTerm * Eglobal)
    (hF : s ^ (-6 : ℝ) * (Real.sqrt sigma)⁻¹ * (3 : ℝ) ^ (s * nr) * F ≤
      B * gapTerm * Data)
    (hgap0 : 0 ≤ gapTerm) (hEg : 0 ≤ Eglobal) (hData : 0 ≤ Data) :
    Elocal ≤ Real.sqrt ((81 : ℝ) ^ d * K) * max A B * gapTerm *
      (Eglobal + Data) := by
  have hsplit : Elocal ≤ Real.sqrt ((81 : ℝ) ^ d * K) *
      (Real.sqrt sigma * (3 : ℝ) ^ (-n) * O +
        s ^ (-6 : ℝ) * (Real.sqrt sigma)⁻¹ * (3 : ℝ) ^ (s * nr) * F) :=
    hbudget.trans (sqrt_projectedEnergyBudget_le hK hsigma hs hO0 hF0)
  exact interiorRowTwo_of_legs hsplit hO hF hgap0 hEg hData

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
