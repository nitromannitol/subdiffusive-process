module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.StoppingWitness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.EntropyGeometric
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.GoodStoppingDepthTail
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.GoodStopping

@[expose] public section

/-!
# Conjunct (4) of `p.cutoff.regularity.good.scales`

This module assembles the good-scale stopping clause
(`e.cutoff.regularity.good.stopping.tail` and
`e.cutoff.regularity.good.stopping`) in the
exact frozen shape, from three proved inputs:

* the finite-cutoff bad-density union bound
  `Section6Cutoff.exists_measure_cutoffGoodStoppingDepth_tail_le_sum_exp`,
  which still carries the spatial-entropy factor `3^{d(m-n)}`;
* `sum_entropy_exp_le`, which absorbs that factor and leaves a geometric
  tail; and
* `exists_stopping_witness_ogammaLE_of_le`, which converts the tail into the
  frozen `O_{Γ_1}` carrier on a measurable index dominated by the literal
  `goodStoppingIndex`.

The pathwise half is `Section6Stopping.badScaleCount_lt_of_le_goodStoppingIndex`,
which is already generic in the cutoff.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The entropy budget of dimension `d`: the union bound over the `3^{d k}`
translated centres costs this much exponential rate per scale. -/
noncomputable def entropyBudget (d : ℕ) : ℝ :=
  (d : ℝ) * Real.log 3 + Real.log 2

theorem entropyBudget_pos (d : ℕ) : 0 < entropyBudget d := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : (0 : ℝ) ≤ (d : ℝ) * Real.log 3 :=
    mul_nonneg (Nat.cast_nonneg d) (Real.log_nonneg (by norm_num))
  unfold entropyBudget
  linarith

/-- The parameter arithmetic of conjunct (4), isolated over plain reals:
the frozen smallness hypothesis simultaneously discharges the proved union
bound's hypothesis, meets the entropy budget, and identifies the sharp
`O_{Γ_1}` scale. -/
private theorem good_stopping_arith
    {C0 B s eps lam DD : ℝ}
    (hC0 : 0 < C0) (hB : 0 < B) (hs : 0 < s) (heps : 0 < eps)
    (hlam : 0 < lam) (hDD : 0 < DD)
    (hkey : C0 * (16 * (1 + Real.log 2) + 4 * B + 2) *
        ((s ^ 6)⁻¹ * (eps⁻¹ ^ 2 * DD)) ≤ lam) :
    C0 * ((s ^ 6)⁻¹ * (eps⁻¹ ^ 2 * DD)) ≤ lam / 2 ∧
    B ≤ (s ^ 6 * eps ^ 2 * (lam / 2) / (C0 * DD)) / 2 ∧
    4 * ((1 + Real.log 2) /
        ((s ^ 6 * eps ^ 2 * (lam / 2) / (C0 * DD)) / 2)) =
      16 * (1 + Real.log 2) * C0 * ((s ^ 6)⁻¹ * (eps⁻¹ ^ 2 * DD)) * lam⁻¹ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs6 : (0 : ℝ) < s ^ 6 := pow_pos hs 6
  have heps2 : (0 : ℝ) < eps ^ 2 := pow_pos heps 2
  have hepsinv : (0 : ℝ) < eps⁻¹ ^ 2 := pow_pos (inv_pos.mpr heps) 2
  set P : ℝ := (s ^ 6)⁻¹ * (eps⁻¹ ^ 2 * DD) with hPdef
  have hP : 0 < P := by
    rw [hPdef]
    exact mul_pos (inv_pos.mpr hs6) (mul_pos hepsinv hDD)
  have hPid : P * (s ^ 6 * eps ^ 2) = DD := by
    rw [hPdef]
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [hP, hC0, hB, hlog2, hkey]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2),
      le_div_iff₀ (mul_pos hC0 hDD)]
    have hscaled := mul_le_mul_of_nonneg_right hkey
      (mul_pos hs6 heps2).le
    rw [mul_assoc, hPid] at hscaled
    have hcoeff : C0 * (4 * B) ≤ C0 * (16 * (1 + Real.log 2) + 4 * B + 2) := by
      nlinarith [hC0, hlog2]
    have hexpand : C0 * (4 * B) * DD ≤
        C0 * (16 * (1 + Real.log 2) + 4 * B + 2) * DD :=
      mul_le_mul_of_nonneg_right hcoeff hDD.le
    nlinarith [hexpand, hscaled]
  · rw [hPdef]
    field_simp
    ring

/-- Conjunct (4) of the frozen finite-cutoff good-scale proposition. -/
theorem exists_cutoff_regularity_good_stopping_clause (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, ∀ L : ℕ,
      ∀ s ∈ Set.Ioc 0 (1 / 2 : ℝ),
        C * M.delta ^ 2 * |Real.log M.delta| ≤ s →
        ∀ epsilon ∈ Set.Ioc 0 1, ∀ lambda ∈ Set.Ioc (0 : ℝ) 1,
          C * s ^ (-8 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
              |Real.log M.delta| ≤ lambda →
          ∀ m : ℕ, ∃ X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℤ,
            (∀ omega, X omega ∈ Set.Icc (-1 : ℤ) m) ∧
            SubdiffusiveProcess.OGammaLE M.P.toMeasure 1
              (C * s ^ (-8 : ℤ) * epsilon⁻¹ ^ 2 * lambda⁻¹ *
                M.delta ^ 2 * |Real.log M.delta|)
              (fun omega => max ((((m : ℤ) - X omega).toNat : ℝ) - 1) 0) ∧
            (∀ omega, 0 ≤ (m : ℤ) - X omega ∧
              ∀ n : ℕ, (n : ℤ) ≤ X omega →
                ∀ z : Vec d, OnTriadicGrid n z → z ∈ cube d m →
                  (∑ j ∈ Finset.Icc n m,
                    (1 - if omega ∈ goodEvent M (some L) j z epsilon s then 1
                      else 0)) <
                    1 + lambda * ((m : ℝ) - (n : ℝ))) := by
  obtain ⟨C0, hC0, hStoppingTail⟩ :=
    Section6Cutoff.exists_measure_cutoffGoodStoppingDepth_tail_le_sum_exp d
  have hB : 0 < entropyBudget d := entropyBudget_pos d
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C0 * (16 * (1 + Real.log 2) + 4 * entropyBudget d + 2), by positivity,
    ?_⟩
  set C : ℝ := C0 * (16 * (1 + Real.log 2) + 4 * entropyBudget d + 2) with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  intro M L s hs _hsdelta epsilon hepsilon lambda hlambda hlam2 m
  obtain ⟨hs0, hs2⟩ := hs
  obtain ⟨he0, he1⟩ := hepsilon
  obtain ⟨hl0, hl1⟩ := hlambda
  have hs1 : s ≤ 1 := hs2.trans (by norm_num)
  have hd0 : 0 < M.delta := M.shellPrefix.delta_pos
  have hdhalf : M.delta ≤ 1 / 2 := M.shellPrefix.delta_le_half
  have hlogneg : Real.log M.delta < 0 :=
    Real.log_neg hd0 (hdhalf.trans_lt (by norm_num))
  have hlogpos : 0 < |Real.log M.delta| := abs_pos.mpr hlogneg.ne
  set DD : ℝ := M.delta ^ 2 * |Real.log M.delta| with hDDdef
  have hDD : 0 < DD := by
    rw [hDDdef]
    exact mul_pos (pow_pos hd0 2) hlogpos
  have hz6 : s ^ (-6 : ℤ) = (s ^ (6 : ℕ))⁻¹ := by
    rw [show (-6 : ℤ) = -(6 : ℕ) by norm_num, zpow_neg, zpow_natCast]
  have hz8 : s ^ (-8 : ℤ) = (s ^ (8 : ℕ))⁻¹ := by
    rw [show (-8 : ℤ) = -(8 : ℕ) by norm_num, zpow_neg, zpow_natCast]
  have hs68 : (s ^ (6 : ℕ))⁻¹ ≤ (s ^ (8 : ℕ))⁻¹ := by
    have h68 : s ^ (8 : ℕ) ≤ s ^ (6 : ℕ) :=
      pow_le_pow_of_le_one hs0.le hs1 (by norm_num)
    simpa [one_div] using one_div_le_one_div_of_le (pow_pos hs0 8) h68
  have hPpos : (0 : ℝ) < (s ^ (6 : ℕ))⁻¹ * (epsilon⁻¹ ^ 2 * DD) :=
    mul_pos (inv_pos.mpr (pow_pos hs0 6))
      (mul_pos (pow_pos (inv_pos.mpr he0) 2) hDD)
  -- the frozen hypothesis, transported to the `s^{-6}` scale
  have hkey : C * ((s ^ (6 : ℕ))⁻¹ * (epsilon⁻¹ ^ 2 * DD)) ≤ lambda := by
    refine le_trans ?_ hlam2
    have hmono : C * ((s ^ (6 : ℕ))⁻¹ * (epsilon⁻¹ ^ 2 * DD)) ≤
        C * ((s ^ (8 : ℕ))⁻¹ * (epsilon⁻¹ ^ 2 * DD)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hs68 (by positivity)) hCpos.le
    refine hmono.trans_eq ?_
    rw [hz8, hDDdef]; ring
  obtain ⟨harith1, harith2, harith3⟩ :=
    good_stopping_arith (C0 := C0) (B := entropyBudget d) (s := s)
      (eps := epsilon) (lam := lambda) (DD := DD) hC0 hB hs0 he0 hl0 hDD
      (by rw [hCdef] at hkey; exact hkey)
  have hsmall : C0 * s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
      |Real.log M.delta| ≤ lambda / 2 := by
    refine le_trans (le_of_eq ?_) harith1
    rw [hz6, hDDdef]; ring
  set rate : ℝ := s ^ 6 * epsilon ^ 2 * (lambda / 2) /
    (C0 * M.delta ^ 2 * |Real.log M.delta|) with hratedef
  have hratepos : 0 < rate := by
    rw [hratedef]
    refine div_pos (mul_pos (mul_pos (pow_pos hs0 6) (pow_pos he0 2))
      (by linarith)) ?_
    exact mul_pos (mul_pos hC0 (pow_pos hd0 2)) hlogpos
  have hrateDD : rate = s ^ 6 * epsilon ^ 2 * (lambda / 2) / (C0 * DD) := by
    rw [hratedef, hDDdef]
    ring
  have hentropy : entropyBudget d ≤ rate / 2 := by rw [hrateDD]; exact harith2
  -- the literal first-failure index, and its depth tail
  set Jstop : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℤ :=
    fun omega => (goodStoppingIndex M (some L) lambda epsilon s m omega : ℤ)
    with hJstopdef
  have hJ : ∀ omega, Jstop omega ∈ Set.Icc (-1 : ℤ) (m : ℤ) := fun omega =>
    (goodStoppingIndex M (some L) lambda epsilon s m omega).property
  have htail : ∀ q : ℕ, 0 < q →
      M.P.toMeasure.real {omega | q < ((m : ℤ) - Jstop omega).toNat} ≤
        2 * Real.exp (-(rate / 2 * (q : ℝ))) := by
    intro q _hq
    have hset : {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d |
          q < ((m : ℤ) - Jstop omega).toNat} =
        {omega | q <
          Section6Stopping.cutoffGoodStoppingDepth M L lambda epsilon s m omega} :=
      rfl
    by_cases hqm : q ≤ m
    · have hE := hStoppingTail M L s lambda epsilon ⟨hs0, hs1⟩ ⟨hl0, hl1⟩
        ⟨he0, he1⟩ hsmall q m
      have hfin : ∀ n ∈ Finset.range (m - q + 1),
          ((3 ^ (d * (m - n)) : ℕ) : ℝ≥0∞) *
            ENNReal.ofReal (Real.exp (-rate * ((m : ℝ) - (n : ℝ) + 1))) ≠ ⊤ :=
        fun n _ => ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
          ENNReal.ofReal_ne_top
      have hsum_ne_top :
          (∑ n ∈ Finset.range (m - q + 1),
            ((3 ^ (d * (m - n)) : ℕ) : ℝ≥0∞) *
              ENNReal.ofReal (Real.exp (-rate * ((m : ℝ) - (n : ℝ) + 1))))
            ≠ ⊤ := ENNReal.sum_ne_top.2 hfin
      have hreal := ENNReal.toReal_mono hsum_ne_top hE
      rw [ENNReal.toReal_sum hfin] at hreal
      have hterms : ∀ n ∈ Finset.range (m - q + 1),
          (((3 ^ (d * (m - n)) : ℕ) : ℝ≥0∞) *
            ENNReal.ofReal
              (Real.exp (-rate * ((m : ℝ) - (n : ℝ) + 1)))).toReal =
            ((3 ^ (d * (m - n)) : ℕ) : ℝ) *
              Real.exp (-rate * ((m : ℝ) - (n : ℝ) + 1)) := by
        intro n _
        rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
          ENNReal.toReal_ofReal (Real.exp_pos _).le]
      rw [Finset.sum_congr rfl hterms] at hreal
      rw [hset]
      exact hreal.trans (sum_entropy_exp_le hqm hratepos hentropy)
    · have hempty : {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d |
          q < ((m : ℤ) - Jstop omega).toNat} = ∅ := by
        ext omega
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
          not_lt]
        have h := (hJ omega).1
        omega
      rw [hempty, measureReal_empty]
      positivity
  have hscale : depthGammaOneScaleSharp 2 (rate / 2) ≤
      C * s ^ (-8 : ℤ) * epsilon⁻¹ ^ 2 * lambda⁻¹ * M.delta ^ 2 *
        |Real.log M.delta| := by
    have hsharp : depthGammaOneScaleSharp 2 (rate / 2) =
        16 * (1 + Real.log 2) * C0 *
          ((s ^ (6 : ℕ))⁻¹ * (epsilon⁻¹ ^ 2 * DD)) * lambda⁻¹ := by
      rw [depthGammaOneScaleSharp, depthTailScaleSharp, hrateDD]
      simpa using harith3
    rw [hsharp]
    have hlinv : (0 : ℝ) < lambda⁻¹ := inv_pos.mpr hl0
    have h16 : 16 * (1 + Real.log 2) * C0 ≤ C := by
      rw [hCdef]; nlinarith [hC0.le, hB.le, hlog2.le]
    have hstep : 16 * (1 + Real.log 2) * C0 *
        ((s ^ (6 : ℕ))⁻¹ * (epsilon⁻¹ ^ 2 * DD)) ≤
        C * ((s ^ (8 : ℕ))⁻¹ * (epsilon⁻¹ ^ 2 * DD)) := by
      refine (mul_le_mul_of_nonneg_right h16 hPpos.le).trans ?_
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hs68 (by positivity)) hCpos.le
    calc 16 * (1 + Real.log 2) * C0 *
          ((s ^ (6 : ℕ))⁻¹ * (epsilon⁻¹ ^ 2 * DD)) * lambda⁻¹
        ≤ C * ((s ^ (8 : ℕ))⁻¹ * (epsilon⁻¹ ^ 2 * DD)) * lambda⁻¹ :=
          mul_le_mul_of_nonneg_right hstep hlinv.le
      _ = C * s ^ (-8 : ℤ) * epsilon⁻¹ ^ 2 * lambda⁻¹ * M.delta ^ 2 *
            |Real.log M.delta| := by rw [hz8, hDDdef]; ring
  obtain ⟨X, hrange, hdom, hog⟩ :=
    exists_stopping_witness_ogammaLE_of_le (μ := M.P.toMeasure) m Jstop hJ
      (by norm_num : (1 : ℝ) ≤ 2) (by positivity : (0:ℝ) < rate / 2)
      hscale htail
  refine ⟨X, hrange, hog, ?_⟩
  intro omega
  refine ⟨by have := (hrange omega).2; omega, ?_⟩
  intro n hn z hzgrid hzmem
  refine Section6Stopping.badScaleCount_lt_of_le_goodStoppingIndex
    M (some L) lambda epsilon s m n omega ?_ z hzgrid hzmem
  exact hn.trans (hdom omega)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
