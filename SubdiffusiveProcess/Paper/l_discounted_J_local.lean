module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.ResponseDensity

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Paper

/-- The discounted response test at discount `3^{-s (m-n)}` fails iff the frozen `GoodResponse` fails at `8 s`. -/
theorem aux_l_discounted_J_local_iff {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ)
    (epsilon s : ℝ) (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    (∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
        ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d j \ cube d (j - 1) ∧
          ∃ e : Vec d, Homogenization.vecNormSq e = 1 ∧
            epsilon ^ 2 < (3 : ℝ) ^ (-(s * ((m : ℝ) - (n : ℝ)))) *
              section6Response M n n ω z e) ↔
      ω ∈ {ω' : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d |
        GoodResponse M none m 0 epsilon (8 * s) ω'}ᶜ := by
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, GoodResponse, not_forall, exists_prop, not_le,
    sub_zero, Option.getD_none, min_self]
  refine exists_congr fun j => exists_congr fun n => and_congr Iff.rfl (and_congr Iff.rfl
    (exists_congr fun z => and_congr Iff.rfl (and_congr Iff.rfl
      (exists_congr fun e => and_congr Iff.rfl ?_))))
  have hB : (0 : ℝ) < (3 : ℝ) ^ (-(s * ((m : ℝ) - (n : ℝ)))) := by positivity
  have hA : (0 : ℝ) < (3 : ℝ) ^ ((8 * s * ((m : ℝ) - (n : ℝ))) / 8) := by positivity
  have hAB : (3 : ℝ) ^ ((8 * s * ((m : ℝ) - (n : ℝ))) / 8) *
      (3 : ℝ) ^ (-(s * ((m : ℝ) - (n : ℝ)))) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    have : (8 * s * ((m : ℝ) - (n : ℝ))) / 8 + -(s * ((m : ℝ) - (n : ℝ))) = 0 := by ring
    rw [this, Real.rpow_zero]
  generalize (3 : ℝ) ^ ((8 * s * ((m : ℝ) - (n : ℝ))) / 8) = A at hA hAB ⊢
  generalize (3 : ℝ) ^ (-(s * ((m : ℝ) - (n : ℝ)))) = B at hB hAB ⊢
  generalize section6Response M n n ω z e = J
  constructor
  · intro h
    have h1 := mul_lt_mul_of_pos_left h hA
    calc epsilon ^ 2 * A = A * epsilon ^ 2 := mul_comm _ _
      _ < A * (B * J) := h1
      _ = (A * B) * J := by ring
      _ = J := by rw [hAB, one_mul]
  · intro h
    have h1 := mul_lt_mul_of_pos_right h hB
    calc epsilon ^ 2 = epsilon ^ 2 * (A * B) := by rw [hAB, mul_one]
      _ = epsilon ^ 2 * A * B := by ring
      _ < J * B := h1
      _ = B * J := mul_comm _ _



theorem l_discounted_J_local
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ epsilon s theta : ℝ,
      epsilon ∈ Set.Ioc 0 1 → s ∈ Set.Ioc 0 1 → theta ∈ Set.Ioc 0 1 →
      M.delta ^ 2 * |Real.log M.delta| ≤ C⁻¹ * s ^ 3 * epsilon ^ 2 →
      C * s ^ (-3 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 * |Real.log M.delta| ≤ theta →
      ∀ m0 K : ℕ,
        M.P.toMeasure {ω | theta < (∑ m ∈ Finset.Icc m0 (m0 + K),
            if ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
                ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d j \ cube d (j - 1) ∧
                  ∃ e : Vec d, Homogenization.vecNormSq e = 1 ∧
                    epsilon ^ 2 < (3 : ℝ) ^ (-(s * ((m : ℝ) - (n : ℝ)))) *
                      section6Response M n n ω z e
              then (1 : ℝ) else 0) / (K + 1)} ≤
          ENNReal.ofReal (Real.exp (-(s ^ 3 * epsilon ^ 2 * theta /
            (C * |Real.log M.delta| * M.delta ^ 2)) * (K + 1))) := by
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · exact ⟨1, one_pos, fun M => absurd M.shellPrefix.dimension (by norm_num)⟩
  haveI : NeZero d := ⟨hdpos.ne'⟩
  obtain ⟨C0, hC0, hmain⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.exists_measure_goodResponse_badDensity_le d
  refine ⟨C0, hC0, ?_⟩
  intro M epsilon s theta heps hs htheta _hfirst hsmall m0 K
  have hbound := hmain M s theta epsilon hs htheta heps hsmall m0 K
  refine (MeasureTheory.measure_mono ?_).trans (hbound.trans (le_of_eq ?_))
  · intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    refine hω.le.trans (le_of_eq ?_)
    simp only [SubdiffusiveProcess.CoarseGrainingVocab.intervalEventDensity]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold SubdiffusiveProcess.CoarseGrainingVocab.eventIndicator
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd ((aux_l_discounted_J_local_iff M m epsilon s ω).mp h1) h2
    · exact absurd ((aux_l_discounted_J_local_iff M m epsilon s ω).mpr h2) h1
    · rfl
  · congr 3
    rw [show C0 * M.delta ^ 2 * |Real.log M.delta| = C0 * |Real.log M.delta| * M.delta ^ 2 by ring]

end Paper
