import SubdiffusiveProcess.Frozen.Vocab.InductionHypothesis
import SubdiffusiveProcess.Frozen.Vocab.InductionHypothesisInfinity

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Definition `d.mathcalS.def`, the inductive hypothesis `𝒮(m₀, ξ, δ₁)` of the paper, with `m₀ ∈ ℕ_0` or
`m₀ = ∞` (`m₀ : ℕ∞`; `⊤` is `𝒮(∞, ξ, δ₁)`).

The paper's data are `ξ ∈ [1,∞)` and `δ₁ ∈ (0,1)` (the domain of the definition, kept as conjuncts), and the
statement is
`max_{m ≤ m₀} ‖ max_{|e|=1} J(cu_m, ahom_m^{-1/2} e, ahom_m^{1/2} e; a_m) ‖_{L^ξ(ℙ)} ≤ δ₁`,
where the sphere maximum `max_{|e|=1} J(…)` is `normalizedDefect M m (cu_m)` (frozen vocabulary
`SubdiffusiveProcess.Frozen.Vocab.NormalizedDefect`) and `‖·‖_{L^ξ(ℙ)}` is `paperENNRealLpNorm`.  For `m₀ = ∞` the maximum over
`m ≤ m₀` is the supremum over all `m ∈ ℕ_0`.  The helper lemmas below identify this predicate with the frozen
vocabulary predicates `inductionHypothesis` (finite `m₀`) and `inductionHypothesisInfinity` (`m₀ = ∞`) that
the Section 4--6 statements consume. -/
def d_mathcalS_def {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m0 : ℕ∞) (ξ δ1 : ℝ) : Prop :=
  1 ≤ ξ ∧ 0 < δ1 ∧ δ1 < 1 ∧
    ∀ m : ℕ, (m : ℕ∞) ≤ m0 →
      paperENNRealLpNorm M.P.toMeasure ξ
          (normalizedDefect M m
            (Ch02.cubeDomain (Homogenization.originCube d (m : ℤ)))) ≤
        ENNReal.ofReal δ1

/-- `𝒮(m₀, ξ, δ₁)` for a finite `m₀` is the frozen `inductionHypothesis`. -/
theorem aux_d_mathcalS_def_finite {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (m0 : ℕ) (ξ δ1 : ℝ) :
    d_mathcalS_def M (m0 : ℕ∞) ξ δ1 ↔ inductionHypothesis M m0 ξ δ1 := by
  unfold d_mathcalS_def inductionHypothesis
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_))
  constructor
  · intro h
    refine iSup_le fun m => ?_
    exact h m (by exact_mod_cast Nat.lt_succ_iff.mp m.2)
  · intro h m hm
    have hm' : m ≤ m0 := by exact_mod_cast hm
    exact le_trans (le_iSup (fun m : Fin (m0 + 1) =>
      paperENNRealLpNorm M.P.toMeasure ξ
        (normalizedDefect M m
          (Ch02.cubeDomain (Homogenization.originCube d ((m : ℕ) : ℤ))))) ⟨m, Nat.lt_succ_of_le hm'⟩) h

/-- `𝒮(∞, ξ, δ₁)` is the frozen `inductionHypothesisInfinity`. -/
theorem aux_d_mathcalS_def_infinity {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (ξ δ1 : ℝ) :
    d_mathcalS_def M ⊤ ξ δ1 ↔ inductionHypothesisInfinity M ξ δ1 := by
  unfold d_mathcalS_def inductionHypothesisInfinity
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_))
  constructor
  · intro h
    exact iSup_le fun m => h m le_top
  · intro h m _
    exact le_trans (le_iSup (fun m : ℕ =>
      paperENNRealLpNorm M.P.toMeasure ξ
        (normalizedDefect M m
          (Ch02.cubeDomain (Homogenization.originCube d (m : ℤ))))) m) h

end Paper
