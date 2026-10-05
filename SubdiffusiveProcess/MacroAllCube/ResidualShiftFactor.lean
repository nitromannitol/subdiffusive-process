module

public import SubdiffusiveProcess.MacroAllCube.ResidualNormalization
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.AnnularRecombination

@[expose] public section

/-!
# The homogenized factor in the residual coefficient shift

coefficient identity (`MacroAllCube.normalized_coefficient_shift`) writes
the physical coefficient of `M` at cutoff `n + k` on a root of side `r = s 3^-k`
as a random multiple of the coefficient of `M_s` at cutoff `n`, with factor

```text
c_{n,k} = [ahom(M_s, n) / ahom(M, n + k)] * exp(A_k - k τ²) .
```

With the exact normalization `ahom(M_s, n) = ahom(M, n)` and the upstream
annealed ordering `cutoff_ahom_ratio_ordering`, the deterministic part of this
factor is bounded uniformly in `n`:

```text
1 ≤ ahom(M_s, n) / ahom(M, n + k) ≤ exp(2 τ² k) .
```
-/

open _root_.SubdiffusiveProcess.Model

noncomputable section

namespace ResidualNormalization

variable {d : ℕ}

/-- **`n`-uniform bound on the homogenized ratio of the residual shift.** -/
theorem residual_ahom_shift_ratio (M : GMCModel d) {s : ℝ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3)
    (hδ : M.delta ≤ (2 * ResidualModel.residualDisorderFactor d)⁻¹) (n k : ℕ) :
    1 ≤ SubdiffusiveProcess.CoarseGrainingVocab.ahom (ResidualModel.residualModel M hs1 hs3 hδ) n /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M (n + k) ∧
      SubdiffusiveProcess.CoarseGrainingVocab.ahom (ResidualModel.residualModel M hs1 hs3 hδ) n /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M (n + k) ≤
        Real.exp (2 * tauSq M.P * (k : ℝ)) := by
  rw [ahom_residualModel M hs1 hs3 hδ n]
  have h := SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.cutoff_ahom_ratio_ordering M (n + k)
    (Nat.le_add_right n k)
  rw [min_eq_left (Nat.le_add_right n k), min_self, Nat.add_sub_cancel_left] at h
  exact h

end ResidualNormalization

