module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.ProviderSupport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.DensityClause
public import SubdiffusiveProcess.Section6.MeasurableErrorStoppingClause
public import SubdiffusiveProcess.Section6.MeasurableGoodStoppingClause

@[expose] public section

/-!
# Provider for `p.cutoff.regularity.good.scales`

The five conjuncts are discharged separately in
`SubdiffusiveProcess/CoarseGrainingVocab/Section6CutoffRegularity/`:

| # | clause |
|---|---|
| (1) density | `exists_cutoff_regularity_density_clause` |
| (2) error average | `exists_cutoff_regularity_error_average_clause` |
| (3) error stopping | `exists_measurable_cutoff_regularity_error_stopping_clause` |
| (4) good stopping | `exists_measurable_cutoff_regularity_good_stopping_clause` |
| (5) good-scale error | `exists_cutoff_regularity_good_scale_clause` |

This module does the two things that remain.

**One constant.**  Each clause supplies its own; the anchor asks for one.  The
sum works because every conjunct is monotone in `C` in the same direction:
raising `C` strengthens each hypothesis and weakens each conclusion.  For
conjunct (2) it also *shrinks* the subtracted observable, which
`ogammaLE_mono_observable` absorbs; for conjuncts (3) and (4) the conclusion is
an `OGammaLE` over an existentially produced measurable witness, which is what
`ProviderSupport.ogammaLE_mono_scale'` is for.

**Dimension zero.**  Conjuncts (2) and (3) carry `[NeZero d]` while the anchor
quantifies over every `d`.  The `d = 0` case is not vacuous by subsingleton
collapse of `Vec 0` — it is vacuous because there are **no models**:
`M.shellPrefix.dimension : 2 ≤ d` is uninhabitable at `d = 0`.  So the branch is
discharged honestly from the model itself rather than from the shape of the
conclusion.
-/

namespace SubdiffusiveProcess.Section6

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

/-- `X / q ≤ X / p` for `0 ≤ X` and `0 < p ≤ q`. -/
private theorem div_le_div_of_le_denom {X p q : ℝ} (hX : 0 ≤ X) (hp : 0 < p)
    (hpq : p ≤ q) : X / q ≤ X / p := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left
    (by simpa [one_div] using one_div_le_one_div_of_le hp hpq) hX

-- Measurable strengthening of the existing complete native provider.
theorem cutoff_regularity_good_scales_measurable
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ L : ℕ,
      (∀ s epsilon theta : ℝ, s ∈ Set.Ioc 0 1 → epsilon ∈ Set.Ioc 0 1 →
        theta ∈ Set.Ioc 0 1 →
        C * s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 * |Real.log M.delta| ≤ theta →
        ∀ m0 K : ℕ,
          M.P.toMeasure {ω | (∑ m ∈ Finset.Icc m0 (m0 + K),
              if ω ∈ goodEvent M (some L) m 0 epsilon s then (1 : ℝ) else 0) /
                (K + 1) ≤ 1 - theta} ≤
            ENNReal.ofReal (Real.exp (-(s ^ 6 * epsilon ^ 2 * theta /
              (C * M.delta ^ 2 * |Real.log M.delta|)) * (K + 1)))) ∧
      (∀ s ∈ Set.Ioc 0 (1 / 2 : ℝ),
        C * M.delta ^ 2 * |Real.log M.delta| ≤ s → ∀ n m : ℕ, n ≤ m →
          ∀ z : Vec d,
            OGammaLE M.P.toMeasure 2
              (C * s ^ (-7 / 2 : ℝ) * M.delta * Real.sqrt |Real.log M.delta| /
                Real.sqrt (m - n + 1))
              (fun ω => (∑ k ∈ Finset.Icc n m,
                accumulatedError M (some L) k z s ω) / (m - n + 1) -
                  C * s ^ (-7 / 2 : ℝ) * M.delta)) ∧
      (∀ s ∈ Set.Ioc 0 (1 / 2 : ℝ),
        C * M.delta ^ 2 * |Real.log M.delta| ≤ s →
        ∀ lambda ∈ Set.Ioc (0 : ℝ) 1,
          C * s ^ (-7 / 2 : ℝ) * M.delta * Real.sqrt |Real.log M.delta| ≤ lambda →
          ∀ m : ℕ, ∃ X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℤ,
            Measurable X ∧
            (∀ ω, X ω ∈ Set.Icc (-1 : ℤ) m) ∧
            OGammaLE M.P.toMeasure 1
              (C * s ^ (-7 : ℤ) * M.delta ^ 2 * |Real.log M.delta| * lambda⁻¹ ^ 2)
              (fun ω => max ((((m : ℤ) - X ω).toNat : ℝ) - 1) 0) ∧
            (∀ ω, 0 ≤ (m : ℤ) - X ω ∧
              ∀ n : ℕ, (n : ℤ) ≤ X ω →
                ∀ z : Vec d, OnTriadicGrid n z → z ∈ cube d m →
                  ∑ j ∈ Finset.Icc n m, accumulatedError M (some L) j z s ω ≤
                    lambda * ((m : ℝ) - (n : ℝ)))) ∧
      (∀ s ∈ Set.Ioc 0 (1 / 2 : ℝ),
        C * M.delta ^ 2 * |Real.log M.delta| ≤ s →
        ∀ epsilon ∈ Set.Ioc 0 1, ∀ lambda ∈ Set.Ioc (0 : ℝ) 1,
          C * s ^ (-7 / 2 : ℝ) * M.delta * Real.sqrt |Real.log M.delta| ≤ lambda →
          C * s ^ (-8 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
              |Real.log M.delta| ≤ lambda →
          ∀ m : ℕ, ∃ X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℤ,
            Measurable X ∧
            (∀ ω, X ω ∈ Set.Icc (-1 : ℤ) m) ∧
            OGammaLE M.P.toMeasure 1
              (C * s ^ (-8 : ℤ) * epsilon⁻¹ ^ 2 * lambda⁻¹ *
                M.delta ^ 2 * |Real.log M.delta|)
              (fun ω => max ((((m : ℤ) - X ω).toNat : ℝ) - 1) 0) ∧
            (∀ ω, 0 ≤ (m : ℤ) - X ω ∧
              ∀ n : ℕ, (n : ℤ) ≤ X ω →
                ∀ z : Vec d, OnTriadicGrid n z → z ∈ cube d m →
                  (∑ j ∈ Finset.Icc n m,
                    (1 - if ω ∈ goodEvent M (some L) j z epsilon s then 1 else 0)) <
                    1 + lambda * ((m : ℝ) - (n : ℝ)))) ∧
      (∀ s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ),
        ∀ epsilon ∈ Set.Icc (s⁻¹ * M.delta ^ 2) 1, ∀ m : ℕ, ∀ z : Vec d,
          ∀ ω,
            indicatorValue (goodEvent M (some L) m z epsilon s)
                (fun ω' => section6HomogenizationError M s L m ω' z) ω ≤
              C * min epsilon
                (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 +
                  accumulatedError M (some L) m z s ω) ∧
            indicatorValue (goodEvent M (some L) m z epsilon s)
                (fun ω' => section6HomogenizationError M s L m ω' z) ω ≤ C * epsilon) := by
  by_cases hd : d = 0
  · -- No model exists in dimension zero: `2 ≤ d` is uninhabitable.
    subst hd
    exact ⟨1, one_pos, fun M ↦ absurd M.shellPrefix.dimension (by omega)⟩
  · have : NeZero d := ⟨hd⟩
    obtain ⟨C1, hC1, h1⟩ := exists_cutoff_regularity_density_clause d
    obtain ⟨C2, hC2, h2⟩ := exists_cutoff_regularity_error_average_clause d
    obtain ⟨C3, hC3, h3⟩ := exists_measurable_cutoff_regularity_error_stopping_clause d
    obtain ⟨C4, hC4, h4⟩ := exists_measurable_cutoff_regularity_good_stopping_clause d
    obtain ⟨C5, hC5, h5⟩ := exists_cutoff_regularity_good_scale_clause d
    refine ⟨C1 + C2 + C3 + C4 + C5, by positivity, ?_⟩
    set C : ℝ := C1 + C2 + C3 + C4 + C5 with hCdef
    have hC : 0 < C := by rw [hCdef]; positivity
    have h1C : C1 ≤ C := by rw [hCdef]; linarith
    have h2C : C2 ≤ C := by rw [hCdef]; linarith
    have h3C : C3 ≤ C := by rw [hCdef]; linarith
    have h4C : C4 ≤ C := by rw [hCdef]; linarith
    have h5C : C5 ≤ C := by rw [hCdef]; linarith
    intro M L
    have hdel : 0 < M.delta := M.shellPrefix.delta_pos
    have hlogNeg : Real.log M.delta < 0 :=
      Real.log_neg hdel (M.shellPrefix.delta_le_half.trans_lt (by norm_num))
    have hlogpos : 0 < |Real.log M.delta| := abs_pos.mpr hlogNeg.ne
    have hbase : (0 : ℝ) < M.delta ^ 2 * |Real.log M.delta| := by positivity
    -- the shared "budget hypothesis is stronger at the larger constant" step
    have hbudget : ∀ {c : ℝ}, c ≤ C → ∀ {s : ℝ},
        C * M.delta ^ 2 * |Real.log M.delta| ≤ s →
        c * M.delta ^ 2 * |Real.log M.delta| ≤ s := by
      intro c hc s hs
      refine le_trans ?_ hs
      calc c * M.delta ^ 2 * |Real.log M.delta|
          = c * (M.delta ^ 2 * |Real.log M.delta|) := by ring
        _ ≤ C * (M.delta ^ 2 * |Real.log M.delta|) :=
            mul_le_mul_of_nonneg_right hc hbase.le
        _ = C * M.delta ^ 2 * |Real.log M.delta| := by ring
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- (1) density
      intro s epsilon theta hs hepsilon htheta hsmall m0 K
      have hs0 : 0 < s := hs.1
      have heps0 : 0 < epsilon := hepsilon.1
      have htheta0 : 0 < theta := htheta.1
      have hspow : (0 : ℝ) < s ^ (-6 : ℤ) := zpow_pos hs0 _
      have hfac : (0 : ℝ) ≤ s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
          |Real.log M.delta| :=
        mul_nonneg (mul_nonneg (mul_nonneg hspow.le (sq_nonneg _)) (sq_nonneg _))
          (abs_nonneg _)
      refine (h1 M L s epsilon theta hs hepsilon htheta ?_ m0 K).trans ?_
      · refine le_trans ?_ hsmall
        calc C1 * s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 * |Real.log M.delta|
            = C1 * (s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
              |Real.log M.delta|) := by ring
          _ ≤ C * (s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
              |Real.log M.delta|) := mul_le_mul_of_nonneg_right h1C hfac
          _ = C * s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
              |Real.log M.delta| := by ring
      · refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
        have hnum : (0 : ℝ) ≤ s ^ 6 * epsilon ^ 2 * theta := by positivity
        have hden1 : (0 : ℝ) < C1 * M.delta ^ 2 * |Real.log M.delta| := by
          have hre : C1 * M.delta ^ 2 * |Real.log M.delta| =
              C1 * (M.delta ^ 2 * |Real.log M.delta|) := by ring
          rw [hre]
          exact mul_pos hC1 hbase
        have hdenle : C1 * M.delta ^ 2 * |Real.log M.delta| ≤
            C * M.delta ^ 2 * |Real.log M.delta| := by
          calc C1 * M.delta ^ 2 * |Real.log M.delta|
              = C1 * (M.delta ^ 2 * |Real.log M.delta|) := by ring
            _ ≤ C * (M.delta ^ 2 * |Real.log M.delta|) :=
                mul_le_mul_of_nonneg_right h1C hbase.le
            _ = C * M.delta ^ 2 * |Real.log M.delta| := by ring
        have hdiv := div_le_div_of_le_denom hnum hden1 hdenle
        have hK : (0 : ℝ) ≤ (K : ℝ) + 1 := by positivity
        have hstep := mul_le_mul_of_nonneg_right hdiv hK
        rw [neg_mul, neg_mul, neg_le_neg_iff]
        exact hstep
    · -- (2) error average
      intro s hs hsmall n m hnm z
      have hs0 : 0 < s := hs.1
      have hbase2 := h2 M L s hs (hbudget h2C hsmall) n m hnm z
      have hQ0 : (0 : ℝ) ≤ s ^ (-7 / 2 : ℝ) * M.delta :=
        mul_nonneg (Real.rpow_pos_of_pos hs0 _).le hdel.le
      have hLam : (0 : ℝ) < Real.sqrt |Real.log M.delta| :=
        Real.sqrt_pos.mpr hlogpos
      have hQL0 : (0 : ℝ) ≤ s ^ (-7 / 2 : ℝ) * M.delta *
          Real.sqrt |Real.log M.delta| := mul_nonneg hQ0 hLam.le
      have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      have hW0 : (0 : ℝ) < (m : ℝ) - (n : ℝ) + 1 := by linarith
      have hsqrtW : (0 : ℝ) < Real.sqrt ((m : ℝ) - (n : ℝ) + 1) :=
        Real.sqrt_pos.mpr hW0
      have hobs : Measurable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦
          (∑ k ∈ Finset.Icc n m, accumulatedError M (some L) k z s omega) /
              ((m : ℝ) - (n : ℝ) + 1) - C * s ^ (-7 / 2 : ℝ) * M.delta) :=
        ((Finset.measurable_sum _ fun k _ ↦
          measurable_accumulatedError M (some L) k z s).div_const _).sub_const _
      have hscalepos : (0 : ℝ) <
          C2 * s ^ (-7 / 2 : ℝ) * M.delta * Real.sqrt |Real.log M.delta| /
            Real.sqrt ((m : ℝ) - (n : ℝ) + 1) := by
        have hnumpos : (0 : ℝ) < C2 * s ^ (-7 / 2 : ℝ) * M.delta *
            Real.sqrt |Real.log M.delta| := by
          have h1 : (0 : ℝ) < s ^ (-7 / 2 : ℝ) := Real.rpow_pos_of_pos hs0 _
          exact mul_pos (mul_pos (mul_pos hC2 h1) hdel) hLam
        exact div_pos hnumpos hsqrtW
      have hQmono : C2 * s ^ (-7 / 2 : ℝ) * M.delta ≤
          C * s ^ (-7 / 2 : ℝ) * M.delta := by
        calc C2 * s ^ (-7 / 2 : ℝ) * M.delta
            = C2 * (s ^ (-7 / 2 : ℝ) * M.delta) := by ring
          _ ≤ C * (s ^ (-7 / 2 : ℝ) * M.delta) :=
              mul_le_mul_of_nonneg_right h2C hQ0
          _ = C * s ^ (-7 / 2 : ℝ) * M.delta := by ring
      have hstep := ogammaLE_mono_observable (by norm_num) hscalepos hobs
        (Filter.Eventually.of_forall (fun _ ↦ by linarith [hQmono])) hbase2
      refine ogammaLE_mono_scale' (by norm_num) hscalepos ?_ hstep
      refine div_le_div_of_le_nonneg ?_ (Real.sqrt_nonneg _)
      calc C2 * s ^ (-7 / 2 : ℝ) * M.delta * Real.sqrt |Real.log M.delta|
          = C2 * (s ^ (-7 / 2 : ℝ) * M.delta *
            Real.sqrt |Real.log M.delta|) := by ring
        _ ≤ C * (s ^ (-7 / 2 : ℝ) * M.delta *
            Real.sqrt |Real.log M.delta|) :=
            mul_le_mul_of_nonneg_right h2C hQL0
        _ = C * s ^ (-7 / 2 : ℝ) * M.delta *
            Real.sqrt |Real.log M.delta| := by ring
    · -- (3) error stopping
      intro s hs hsmall lambda hlambda hlam m
      have hs0 : 0 < s := hs.1
      have hl0 : 0 < lambda := hlambda.1
      have hQ0 : (0 : ℝ) ≤ s ^ (-7 / 2 : ℝ) * M.delta :=
        mul_nonneg (Real.rpow_pos_of_pos hs0 _).le hdel.le
      have hQL0 : (0 : ℝ) ≤ s ^ (-7 / 2 : ℝ) * M.delta *
          Real.sqrt |Real.log M.delta| := mul_nonneg hQ0 (Real.sqrt_nonneg _)
      have hlam3 : C3 * s ^ (-7 / 2 : ℝ) * M.delta *
          Real.sqrt |Real.log M.delta| ≤ lambda := by
        refine le_trans ?_ hlam
        calc C3 * s ^ (-7 / 2 : ℝ) * M.delta * Real.sqrt |Real.log M.delta|
            = C3 * (s ^ (-7 / 2 : ℝ) * M.delta *
              Real.sqrt |Real.log M.delta|) := by ring
          _ ≤ C * (s ^ (-7 / 2 : ℝ) * M.delta *
              Real.sqrt |Real.log M.delta|) :=
              mul_le_mul_of_nonneg_right h3C hQL0
          _ = C * s ^ (-7 / 2 : ℝ) * M.delta *
              Real.sqrt |Real.log M.delta| := by ring
      obtain ⟨X, hX, hrange, hog, hpath⟩ :=
        h3 M L s hs (hbudget h3C hsmall) lambda hlambda hlam3 m
      refine ⟨X, hX, hrange, ?_, hpath⟩
      have hspos : (0 : ℝ) < s ^ (-7 : ℤ) := zpow_pos hs0 _
      have hli : (0 : ℝ) < lambda⁻¹ ^ 2 := by positivity
      have hrest : (0 : ℝ) ≤ s ^ (-7 : ℤ) * M.delta ^ 2 * |Real.log M.delta| *
          lambda⁻¹ ^ 2 :=
        mul_nonneg (mul_nonneg (mul_nonneg hspos.le (sq_nonneg _))
          (abs_nonneg _)) hli.le
      have hpos3 : (0 : ℝ) < C3 * s ^ (-7 : ℤ) * M.delta ^ 2 *
          |Real.log M.delta| * lambda⁻¹ ^ 2 := by
        have hre : C3 * s ^ (-7 : ℤ) * M.delta ^ 2 * |Real.log M.delta| *
            lambda⁻¹ ^ 2 = C3 * (s ^ (-7 : ℤ) * M.delta ^ 2 *
              |Real.log M.delta| * lambda⁻¹ ^ 2) := by ring
        rw [hre]
        exact mul_pos hC3 (by
          exact mul_pos (mul_pos (mul_pos hspos (by positivity)) hlogpos) hli)
      refine ogammaLE_mono_scale' (by norm_num) hpos3 ?_ hog
      calc C3 * s ^ (-7 : ℤ) * M.delta ^ 2 * |Real.log M.delta| * lambda⁻¹ ^ 2
          = C3 * (s ^ (-7 : ℤ) * M.delta ^ 2 * |Real.log M.delta| *
            lambda⁻¹ ^ 2) := by ring
        _ ≤ C * (s ^ (-7 : ℤ) * M.delta ^ 2 * |Real.log M.delta| *
            lambda⁻¹ ^ 2) := mul_le_mul_of_nonneg_right h3C hrest
        _ = C * s ^ (-7 : ℤ) * M.delta ^ 2 * |Real.log M.delta| *
            lambda⁻¹ ^ 2 := by ring
    · -- (4) good stopping
      intro s hs hsmall epsilon hepsilon lambda hlambda _hlam1 hlam2 m
      have hs0 : 0 < s := hs.1
      have hl0 : 0 < lambda := hlambda.1
      have heps0 : 0 < epsilon := hepsilon.1
      have hspos8 : (0 : ℝ) < s ^ (-8 : ℤ) := zpow_pos hs0 _
      have hei : (0 : ℝ) < epsilon⁻¹ ^ 2 := by positivity
      have hrest8 : (0 : ℝ) ≤ s ^ (-8 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
          |Real.log M.delta| :=
        mul_nonneg (mul_nonneg (mul_nonneg hspos8.le hei.le) (sq_nonneg _))
          (abs_nonneg _)
      have hlam4 : C4 * s ^ (-8 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
          |Real.log M.delta| ≤ lambda := by
        refine le_trans ?_ hlam2
        calc C4 * s ^ (-8 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
              |Real.log M.delta|
            = C4 * (s ^ (-8 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
              |Real.log M.delta|) := by ring
          _ ≤ C * (s ^ (-8 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
              |Real.log M.delta|) := mul_le_mul_of_nonneg_right h4C hrest8
          _ = C * s ^ (-8 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
              |Real.log M.delta| := by ring
      obtain ⟨X, hX, hrange, hog, hpath⟩ :=
        h4 M L s hs (hbudget h4C hsmall) epsilon hepsilon lambda hlambda hlam4 m
      refine ⟨X, hX, hrange, ?_, hpath⟩
      have hlinv : (0 : ℝ) < lambda⁻¹ := by positivity
      have hrest : (0 : ℝ) ≤ s ^ (-8 : ℤ) * epsilon⁻¹ ^ 2 * lambda⁻¹ *
          M.delta ^ 2 * |Real.log M.delta| :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hspos8.le hei.le)
          hlinv.le) (sq_nonneg _)) (abs_nonneg _)
      have hpos4 : (0 : ℝ) < C4 * s ^ (-8 : ℤ) * epsilon⁻¹ ^ 2 * lambda⁻¹ *
          M.delta ^ 2 * |Real.log M.delta| := by
        have hre : C4 * s ^ (-8 : ℤ) * epsilon⁻¹ ^ 2 * lambda⁻¹ *
            M.delta ^ 2 * |Real.log M.delta| = C4 * (s ^ (-8 : ℤ) *
              epsilon⁻¹ ^ 2 * lambda⁻¹ * M.delta ^ 2 *
              |Real.log M.delta|) := by ring
        rw [hre]
        refine mul_pos hC4 ?_
        exact mul_pos (mul_pos (mul_pos (mul_pos hspos8 hei) hlinv)
          (by positivity)) hlogpos
      refine ogammaLE_mono_scale' (by norm_num) hpos4 ?_ hog
      calc C4 * s ^ (-8 : ℤ) * epsilon⁻¹ ^ 2 * lambda⁻¹ * M.delta ^ 2 *
            |Real.log M.delta|
          = C4 * (s ^ (-8 : ℤ) * epsilon⁻¹ ^ 2 * lambda⁻¹ * M.delta ^ 2 *
            |Real.log M.delta|) := by ring
        _ ≤ C * (s ^ (-8 : ℤ) * epsilon⁻¹ ^ 2 * lambda⁻¹ * M.delta ^ 2 *
            |Real.log M.delta|) := mul_le_mul_of_nonneg_right h4C hrest
        _ = C * s ^ (-8 : ℤ) * epsilon⁻¹ ^ 2 * lambda⁻¹ * M.delta ^ 2 *
            |Real.log M.delta| := by ring
    · -- (5) good-scale error
      intro s hs epsilon hepsilon m z omega
      obtain ⟨h51, h52⟩ := h5 M L s hs epsilon hepsilon m z omega
      have hs0 : 0 < s :=
        (mul_pos (by norm_num) (sq_pos_of_pos hdel)).trans_le hs.1
      have hD0 : (0 : ℝ) ≤ s⁻¹ * M.delta ^ 2 := by positivity
      have heps0 : 0 ≤ epsilon := hD0.trans hepsilon.1
      have hE0 : 0 ≤ accumulatedError M (some L) m z s omega :=
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.accumulatedError_nonneg
          M (some L) s m z omega
      have hmin0 : 0 ≤ min epsilon (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 +
          accumulatedError M (some L) m z s omega) :=
        le_min heps0 (by positivity)
      exact ⟨h51.trans (mul_le_mul_of_nonneg_right h5C hmin0),
        h52.trans (mul_le_mul_of_nonneg_right h5C heps0)⟩


end

end SubdiffusiveProcess.Section6
