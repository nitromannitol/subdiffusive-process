module

public import SubdiffusiveProcess.EllipticRegularity.Carriers

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Remark `rem_repair`, *The reference coefficient after
reflection*.

The remark reads `lem_repair` and draws the consequence that lets the deterministic
iteration be run for the folded field.  Its three sentences are:

1. `lem_repair` controls the **full** discounted coarse error of the folded
   coefficient at each working scale — not merely a coarse ellipticity bound — and does so
   against a reference scalar that changes from scale to scale but is always the *original*
   one.  That is the hypothesis `herr`/`hbad`/`hratio` below, whose supplier is
   `lem_repair`; the constant is the dimensional `C_d` of `e.ep.j.z.sum`.
2. Hence the accumulated error, the bad-scale count and the reference ratios of `ã_L ∘ T`
   are, up to `C_d`, the original ones.
3. "Correspondingly, the tolerance `ε` in the good events is replaced by `ε/C_d`."  This is
   the operative content, and it is the conclusion proved here: a tolerance met by the
   original quantity at level `ε/C_d` is met by the folded one at level `ε`.

Stating it this way turns a remark about an apparatus into a proposition about three
scale-indexed quantities, which is all any consumer uses.  `prop_folded_iteration` takes
the substitution, as does `prop_neumann_growth`;  both are about the
tolerance, not about the apparatus.

The remark's last sentence — that the substitution is compatible with the parameter order
of `in_iteration` — is a statement about quantifier order, not about these quantities;
it holds because `C_d` depends only on `d`, which is fixed before every parameter in that
order, and is recorded here rather than asserted in Lean. -/
theorem rem_repair :
  ∀ (Cd : ℝ), 0 < Cd →
  ∀ (errOrig errFold badOrig badFold ratioOrig ratioFold : ℕ → ℝ),
    -- `lem_repair` at each working scale, against the original reference scalar
    (∀ j, errFold j ≤ Cd * errOrig j) →
    (∀ j, badFold j ≤ Cd * badOrig j) →
    (∀ j, ratioFold j ≤ Cd * ratioOrig j) →
    -- the tolerance of the good events, tightened by the same dimensional factor
    ∀ eps : ℝ, 0 < eps →
      (∀ j, errOrig j ≤ eps / Cd → errFold j ≤ eps) ∧
      (∀ j, badOrig j ≤ eps / Cd → badFold j ≤ eps) ∧
      (∀ j, ratioOrig j ≤ eps / Cd → ratioFold j ≤ eps) := by
  intro Cd hCd errOrig errFold badOrig badFold ratioOrig ratioFold herr hbad hratio eps _heps
  have key : ∀ (u v : ℕ → ℝ), (∀ j, v j ≤ Cd * u j) → ∀ j, u j ≤ eps / Cd → v j ≤ eps := by
    intro u v huv j hj
    refine (huv j).trans ?_
    calc Cd * u j ≤ Cd * (eps / Cd) := by
          exact mul_le_mul_of_nonneg_left hj hCd.le
      _ = eps := by field_simp
  exact ⟨key _ _ herr, key _ _ hbad, key _ _ hratio⟩

end SubdiffusiveProcess.Paper
