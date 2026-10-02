import SubdiffusiveProcess.Paper.lem_band
import SubdiffusiveProcess.Paper.Foundations.PrefixActualRMeas
import SubdiffusiveProcess.Paper.Foundations.PrefixActualDMeas
import SubdiffusiveProcess.Paper.Foundations.PrefixActualDBlockMeas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Truncated primitive scores

The four literal score formulas of `primitive_scores` at a potential sample (`aux_lfgc_p_trunc_ffull`, `pfull`,
`aux_lfgc_p_trunc_rfull`, `aux_lfgc_p_trunc_dfull`, and the bad score `aux_lfgc_p_trunc_zfull`) and their truncations at depth `L`: the field and
product scores keep the discount depths `j ≤ L` (the product also truncates its tail product at
layer `n + L`), the drift score keeps its gradient series up to layer `n + L`; the response
score is not truncated.  All are measurable in the sample.
-/

open MeasureTheory SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess
open scoped ENNReal BigOperators

namespace Paper
variable {d : ℕ}

/-- The ramp of `primitive_scores`. -/
noncomputable def aux_lfgc_p_trunc_eramp (lo hi : ℝ) (X : ℝ≥0∞) : ℝ :=
  (min (1 : ℝ≥0∞) ((X - ENNReal.ofReal lo) / ENNReal.ofReal (hi - lo))).toReal

/-- The field score formula. -/
noncomputable def aux_lfgc_p_trunc_ffull (s : ℝ) (n : ℕ) (y : Vec d) (g : PotentialSample d) : ℝ≥0∞ :=
  sSup {v : ℝ≥0∞ | ∃ j : ℕ, v = Paper.aux_lem_band_piece_field_term s n y g j}

/-- The field score truncated at discount depth `L`. -/
noncomputable def aux_lfgc_p_trunc_ftr (s : ℝ) (n : ℕ) (y : Vec d) (L : ℕ) (g : PotentialSample d) : ℝ≥0∞ :=
  sSup {v : ℝ≥0∞ | ∃ j : ℕ, j ≤ L ∧ v = Paper.aux_lem_band_piece_field_term s n y g j}

/-- The response score formula. -/
noncomputable def aux_lfgc_p_trunc_rfull (M : GMCModel d) (s : ℝ) (n : ℕ) (y : Vec d) (g : PotentialSample d) :
    ℝ≥0∞ :=
  sSup {v : ℝ≥0∞ | ∃ j l : ℕ, j ≤ n ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
    OnTriadicGrid l (x - y) ∧ x - y ∈ cube d j \ cube d (j - 1) ∧
    v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * ((n : ℝ) - (l : ℝ)) / 8))) * Paper.aux_psf_Jval M l g x}

/-- The first three terms of the drift score formula. -/
noncomputable def aux_lfgc_p_trunc_dhead (M : GMCModel d) (s : ℝ) (n : ℕ) (y : Vec d) (g : PotentialSample d) :
    ℝ≥0∞ :=
  sSup {v : ℝ≥0∞ | ∃ j l : ℕ, j ≤ n ∧ l ≤ n ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
      OnTriadicGrid l (x - y) ∧ x - y ∈ cube d (j : ℤ) \ cube d ((j : ℤ) - 1) ∧
      v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((n : ℝ) - (l : ℝ)))) *
        (min (Paper.aux_psf_Jval M l g x) 1) ^ (1 / 2 : ℝ)} +
    sSup {v : ℝ≥0∞ | ∃ j : ℕ, j ≤ n ∧
      v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((n : ℝ) - (j : ℝ)))) *
        sSup {w : ℝ≥0∞ | ∃ x ∈ translatedCube d (n : ℤ) y,
          w = ENNReal.ofReal |shellBlock n j g x|}} +
    ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (n : ℝ))) *
      sSup {w : ℝ≥0∞ | ∃ x ∈ translatedCube d (n : ℤ) y, w = ENNReal.ofReal |g 0 x|}

/-- One gradient term of the drift score formula. -/
noncomputable def aux_lfgc_p_trunc_dtail (n : ℕ) (y : Vec d) (g : PotentialSample d) (j : ℕ) : ℝ≥0∞ :=
  if n ≤ j then
    ENNReal.ofReal ((3 : ℝ) ^ n) *
      sSup {w : ℝ≥0∞ | ∃ x ∈ translatedCube d (n : ℤ) y,
        w = ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient (g j) x)|}
  else 0

/-- The drift score formula. -/
noncomputable def aux_lfgc_p_trunc_dfull (M : GMCModel d) (s : ℝ) (n : ℕ) (y : Vec d) (g : PotentialSample d) :
    ℝ≥0∞ :=
  aux_lfgc_p_trunc_dhead M s n y g + ∑' j : ℕ, aux_lfgc_p_trunc_dtail n y g j

/-- The drift score with its gradient series truncated at layer `n + L`. -/
noncomputable def aux_lfgc_p_trunc_dtr (M : GMCModel d) (s : ℝ) (n : ℕ) (y : Vec d) (L : ℕ)
    (g : PotentialSample d) : ℝ≥0∞ :=
  aux_lfgc_p_trunc_dhead M s n y g + ∑ j ∈ Finset.range (n + L + 1), aux_lfgc_p_trunc_dtail n y g j

/-- The bad score formula. -/
noncomputable def aux_lfgc_p_trunc_zfull (M : GMCModel d) (s eps : ℝ) (n : ℕ) (y : Vec d)
    (g : PotentialSample d) : ℝ :=
  aux_lfgc_p_trunc_eramp (eps / 2) eps (aux_lfgc_p_trunc_ffull s n y g) +
    aux_lfgc_p_trunc_eramp 6 12 (Paper.aux_lem_band_piece_product_Praw d s n y g) +
    aux_lfgc_p_trunc_eramp (eps ^ 2 / 4) (eps ^ 2) (aux_lfgc_p_trunc_rfull M s n y g)

/-- The bad score with truncated field and product scores. -/
noncomputable def aux_lfgc_p_trunc_ztr (M : GMCModel d) (s eps : ℝ) (n : ℕ) (y : Vec d) (L : ℕ)
    (g : PotentialSample d) : ℝ :=
  aux_lfgc_p_trunc_eramp (eps / 2) eps (aux_lfgc_p_trunc_ftr s n y L g) +
    aux_lfgc_p_trunc_eramp 6 12 (Paper.aux_lem_band_piece_product_trunc_Pcand d s n y g L) +
    aux_lfgc_p_trunc_eramp (eps ^ 2 / 4) (eps ^ 2) (aux_lfgc_p_trunc_rfull M s n y g)

theorem aux_lfgc_p_trunc_measurable_eramp (lo hi : ℝ) (hlohi : lo < hi) : Measurable (aux_lfgc_p_trunc_eramp lo hi) :=
  (Paper.aux_lem_band_piece_product_eramp_continuous lo hi hlohi).measurable

theorem aux_lfgc_p_trunc_measurable_ftr (s : ℝ) (n : ℕ) (y : Vec d) (L : ℕ) :
    Measurable (aux_lfgc_p_trunc_ftr s n y L) :=
  Paper.aux_lem_band_piece_field_trunc_meas s n y L

theorem aux_lfgc_p_trunc_measurable_rfull [NeZero d] (M : GMCModel d) (s : ℝ) (n : ℕ) (y : Vec d) :
    Measurable (aux_lfgc_p_trunc_rfull M s n y) :=
  Paper.aux_lem_prefix_limit_actual_Rsc_meas M s n y

theorem aux_lfgc_p_trunc_measurable_dhead [NeZero d] (M : GMCModel d) (s : ℝ) (n : ℕ) (y : Vec d) :
    Measurable (aux_lfgc_p_trunc_dhead M s n y) :=
  ((Paper.aux_lem_prefix_limit_actual_Dsc_first_meas M s n y).add
    (Paper.aux_dsc_block_meas s n y)).add (Paper.dsc_third_summand_meas s n y)

theorem aux_lfgc_p_trunc_measurable_dtail (n : ℕ) (y : Vec d) (j : ℕ) :
    Measurable (fun g : PotentialSample d => aux_lfgc_p_trunc_dtail n y g j) := by
  unfold aux_lfgc_p_trunc_dtail
  split_ifs
  · refine Measurable.const_mul ?_ _
    refine Paper.aux_lem_band_piece_field_spatial_sup_meas
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.isOpen_translatedCube d n y)
      (fun (g : PotentialSample d) (x : Vec d) =>
        ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient (g j) x)|) ?_ ?_
    · intro g
      exact ENNReal.continuous_ofReal.comp
        ((SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.continuous_euclideanNorm.comp
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.continuous_shellGradient
            (g j))).abs)
    · intro x
      exact ((continuous_abs.measurable.comp
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.continuous_euclideanNorm.measurable.comp
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.measurable_shellGradient_eval x j)))).ennreal_ofReal
  · exact measurable_const

theorem aux_lfgc_p_trunc_measurable_dtr [NeZero d] (M : GMCModel d) (s : ℝ) (n : ℕ) (y : Vec d) (L : ℕ) :
    Measurable (aux_lfgc_p_trunc_dtr M s n y L) :=
  (aux_lfgc_p_trunc_measurable_dhead M s n y).add
    (Finset.measurable_sum _ fun j _ => aux_lfgc_p_trunc_measurable_dtail n y j)

theorem aux_lfgc_p_trunc_measurable_dfull [NeZero d] (M : GMCModel d) (s : ℝ) (n : ℕ) (y : Vec d) :
    Measurable (aux_lfgc_p_trunc_dfull M s n y) :=
  (aux_lfgc_p_trunc_measurable_dhead M s n y).add (Measurable.ennreal_tsum fun j => aux_lfgc_p_trunc_measurable_dtail n y j)

theorem lfgc_p_trunc [NeZero d] (M : GMCModel d) (s eps : ℝ) (heps : 0 < eps) (n : ℕ)
    (y : Vec d) (L : ℕ) : Measurable (aux_lfgc_p_trunc_ztr M s eps n y L) := by
  have h1 : eps / 2 < eps := by linarith
  have h3 : eps ^ 2 / 4 < eps ^ 2 := by have := pow_pos heps 2; linarith
  exact (((aux_lfgc_p_trunc_measurable_eramp _ _ h1).comp (aux_lfgc_p_trunc_measurable_ftr s n y L)).add
    ((aux_lfgc_p_trunc_measurable_eramp 6 12 (by norm_num)).comp
      (Paper.aux_lem_band_piece_product_trunc_Pcand_meas d s n L y))).add
    ((aux_lfgc_p_trunc_measurable_eramp _ _ h3).comp (aux_lfgc_p_trunc_measurable_rfull M s n y))

end Paper
