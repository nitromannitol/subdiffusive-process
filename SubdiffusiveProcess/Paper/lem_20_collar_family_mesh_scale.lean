module

public import SubdiffusiveProcess.Paper.lem_cutoffs
public import SubdiffusiveProcess.Paper.mesh_interpolator

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace Metric
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The comparable triadic scale selected for the arbitrary-width collar,

Scope and inputs:
- `R` and the comparison factor `c` are fixed before the width `r`.
- `hR` and `hc` are the positivity and range conditions needed for the
  first sufficiently fine member of the triadic family.
- `lem_cutoffs` and `mesh_interpolator` supply the triadic mesh family;
  the comparison with an arbitrary real width is concluded here.
- CONCLUDED: one natural-number depth for every `0 < r ≤ 1`, with both
  inequalities needed by the buffered collar construction.
This is a proof-step fine child of `lem_20_collar_family`.
-/
theorem lem_20_collar_family_mesh_scale
    (R c : ℝ) (hR : 0 < R) (hc : 0 < c) (hcR : c ≤ R) :
    ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∃ J : ℕ,
        R / (3 : ℝ) ^ J ≤ c * r ∧
          c * r < 3 * (R / (3 : ℝ) ^ J) := by
  intro r hr hr1
  have hcr : 0 < c * r := mul_pos hc hr
  have hcr_le : c * r ≤ R := by
    have hcr_c : c * r ≤ c := by
      simpa using (mul_le_mul_of_nonneg_left hr1 hc.le)
    exact hcr_c.trans hcR
  have hpow : ∀ n : ℕ, (n : ℝ) ≤ (3 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        rw [pow_succ]
        have hpow_one : (1 : ℝ) ≤ (3 : ℝ) ^ n := by
          exact one_le_pow₀ (by norm_num)
        norm_num at ih ⊢
        nlinarith
  obtain ⟨n, hn⟩ := exists_nat_gt (R / (c * r))
  have hex : ∃ n : ℕ, R ≤ c * r * (3 : ℝ) ^ n := by
    refine ⟨n, ?_⟩
    have hn' : R / (c * r) < (3 : ℝ) ^ n := lt_of_lt_of_le hn (hpow n)
    have := (div_lt_iff₀ hcr).mp hn'
    nlinarith
  let J : ℕ := Nat.find hex
  have hJ : R ≤ c * r * (3 : ℝ) ^ J := Nat.find_spec hex
  have hfirst : R / (3 : ℝ) ^ J ≤ c * r := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (3 : ℝ) ^ J)).2
    nlinarith [hJ]
  have hJ_nonzero : J = 0 ∨ 0 < J := by omega
  rcases hJ_nonzero with hJzero | hJpos
  · refine ⟨0, ?_, ?_⟩
    · simpa [hJzero] using hfirst
    · norm_num
      nlinarith
  · have hprev_not : ¬ R ≤ c * r * (3 : ℝ) ^ (J - 1) := by
      exact Nat.find_min hex (by omega)
    have hprev : c * r * (3 : ℝ) ^ (J - 1) < R := lt_of_not_ge hprev_not
    refine ⟨J, hfirst, ?_⟩
    rw [show 3 * (R / (3 : ℝ) ^ J) = (3 * R) / (3 : ℝ) ^ J by ring]
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < (3 : ℝ) ^ J)).2
    rw [show (3 : ℝ) ^ J = 3 * (3 : ℝ) ^ (J - 1) by
      calc
        (3 : ℝ) ^ J = (3 : ℝ) ^ ((J - 1) + 1) := by
          rw [Nat.sub_add_cancel hJpos]
        _ = (3 : ℝ) ^ (J - 1) * 3 := by rw [pow_succ]
        _ = 3 * (3 : ℝ) ^ (J - 1) := by ring]
    nlinarith

end SubdiffusiveProcess.Paper
