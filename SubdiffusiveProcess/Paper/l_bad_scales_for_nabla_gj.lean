module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.FieldOneDensity

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

namespace SubdiffusiveProcess.Paper

theorem aux_l_bad_scales_for_nabla_gj_translatedCube_zero (d : ℕ) (n : ℤ) :
    translatedCube d n (0 : Vec d) = cube d n := by
  rw [translatedCube]
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    simpa using hy
  · intro x hx
    exact ⟨x, hx, by simp⟩

/-- The discounted field test at discount `3^{-s j}` fails iff the `GoodFieldOne` fails at `8 s`. -/
theorem aux_l_bad_scales_for_nabla_gj_iff {d : ℕ} (m : ℕ) (epsilon s : ℝ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    (∃ j : ℕ, epsilon < (3 : ℝ) ^ (-(s * (j : ℝ))) *
        ∑ i ∈ Finset.Icc (m - j) (m + j),
          supNormOn (cube d ((m : ℤ) + 1 + (j : ℤ))) (fun x =>
            |ω i x| + (3 : ℝ) ^ i *
              Homogenization.euclideanNorm (shellGradient (ω i) x))) ↔
      ω ∈ {ω' : _root_.SubdiffusiveProcess.Model.PotentialSample d |
        GoodFieldOne m 0 epsilon (8 * s) ω'}ᶜ := by
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, GoodFieldOne, not_forall, not_le]
  refine exists_congr fun j => ?_
  rw [aux_l_bad_scales_for_nabla_gj_translatedCube_zero]
  have hB : (0 : ℝ) < (3 : ℝ) ^ (-(s * (j : ℝ))) := by positivity
  have hA : (0 : ℝ) < (3 : ℝ) ^ ((8 * s * (j : ℝ)) / 8) := by positivity
  have hAB : (3 : ℝ) ^ ((8 * s * (j : ℝ)) / 8) * (3 : ℝ) ^ (-(s * (j : ℝ))) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    have : (8 * s * (j : ℝ)) / 8 + -(s * (j : ℝ)) = 0 := by ring
    rw [this, Real.rpow_zero]
  generalize (3 : ℝ) ^ ((8 * s * (j : ℝ)) / 8) = A at hA hAB ⊢
  generalize (3 : ℝ) ^ (-(s * (j : ℝ))) = B at hB hAB ⊢
  generalize (∑ i ∈ Finset.Icc (m - j) (m + j),
    supNormOn (cube d ((m : ℤ) + 1 + (j : ℤ))) (fun x =>
      |ω i x| + (3 : ℝ) ^ i *
        Homogenization.euclideanNorm (shellGradient (ω i) x))) = S
  constructor
  · intro h
    have h1 := mul_lt_mul_of_pos_left h hA
    calc epsilon * A = A * epsilon := mul_comm _ _
      _ < A * (B * S) := h1
      _ = (A * B) * S := by ring
      _ = S := by rw [hAB, one_mul]
  · intro h
    have h1 := mul_lt_mul_of_pos_right h hB
    calc epsilon = epsilon * (A * B) := by rw [hAB, mul_one]
      _ = epsilon * A * B := by ring
      _ < S * B := h1
      _ = B * S := mul_comm _ _



theorem l_bad_scales_for_nabla_gj
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ theta s epsilon : ℝ,
      theta ∈ Set.Ioc 0 1 → s ∈ Set.Ioc 0 1 → epsilon ∈ Set.Ioc 0 1 →
      C * s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 ≤ theta →
      ∀ m0 K : ℕ,
        M.P.toMeasure {ω | theta ≤ (∑ m ∈ Finset.Icc m0 (m0 + K),
            if ∃ j : ℕ, epsilon < (3 : ℝ) ^ (-(s * (j : ℝ))) *
                ∑ i ∈ Finset.Icc (m - j) (m + j),
                  supNormOn (cube d ((m : ℤ) + 1 + (j : ℤ))) (fun x =>
                    |ω i x| + (3 : ℝ) ^ i *
                      Homogenization.euclideanNorm (shellGradient (ω i) x))
              then (1 : ℝ) else 0) / (K + 1)} ≤
          ENNReal.ofReal (Real.exp (-(s ^ 6 * epsilon ^ 2 * theta /
            (C * M.delta ^ 2)) * (K + 1))) := by
  refine ⟨SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.fieldOneDensityConst d,
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.fieldOneDensityConst_pos d, ?_⟩
  intro M theta s epsilon htheta hs heps hsmall m0 K
  have hmain := SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.measure_goodFieldOne_badDensity_le M
    hs.1 hs.2 htheta.1 htheta.2 heps.1 heps.2 hsmall m0 K
  have hset : {ω : _root_.SubdiffusiveProcess.Model.PotentialSample d | theta ≤
      (∑ m ∈ Finset.Icc m0 (m0 + K),
        if ∃ j : ℕ, epsilon < (3 : ℝ) ^ (-(s * (j : ℝ))) *
            ∑ i ∈ Finset.Icc (m - j) (m + j),
              supNormOn (cube d ((m : ℤ) + 1 + (j : ℤ))) (fun x =>
                |ω i x| + (3 : ℝ) ^ i *
                  Homogenization.euclideanNorm (shellGradient (ω i) x))
          then (1 : ℝ) else 0) / (K + 1)} =
      {ω | theta ≤ SubdiffusiveProcess.CoarseGrainingVocab.intervalEventDensity
        (fun m => {ω' : _root_.SubdiffusiveProcess.Model.PotentialSample d |
          GoodFieldOne m 0 epsilon (8 * s) ω'}ᶜ) m0 K ω} := by
    ext ω
    have hsum : (∑ m ∈ Finset.Icc m0 (m0 + K),
        if ∃ j : ℕ, epsilon < (3 : ℝ) ^ (-(s * (j : ℝ))) *
            ∑ i ∈ Finset.Icc (m - j) (m + j),
              supNormOn (cube d ((m : ℤ) + 1 + (j : ℤ))) (fun x =>
                |ω i x| + (3 : ℝ) ^ i *
                  Homogenization.euclideanNorm (shellGradient (ω i) x))
          then (1 : ℝ) else 0) =
        ∑ m ∈ Finset.Icc m0 (m0 + K),
          SubdiffusiveProcess.CoarseGrainingVocab.eventIndicator
            ({ω' : _root_.SubdiffusiveProcess.Model.PotentialSample d |
              GoodFieldOne m 0 epsilon (8 * s) ω'}ᶜ) ω :=
      Finset.sum_congr rfl fun m _ => by
        unfold SubdiffusiveProcess.CoarseGrainingVocab.eventIndicator
        split_ifs with h1 h2 h2
        · rfl
        · exact absurd ((aux_l_bad_scales_for_nabla_gj_iff m epsilon s ω).mp h1) h2
        · exact absurd ((aux_l_bad_scales_for_nabla_gj_iff m epsilon s ω).mpr h2) h1
        · rfl
    simp only [Set.mem_ofPred_eq, SubdiffusiveProcess.CoarseGrainingVocab.intervalEventDensity]
    rw [hsum]
  rw [hset]
  exact hmain

end SubdiffusiveProcess.Paper
