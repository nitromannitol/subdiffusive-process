module

public import SubdiffusiveProcess.Static.CutoffBlockComparison
public import SubdiffusiveProcess.Providers.Section3.AnnealedMatrixBounds
public import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments
public import SubdiffusiveProcess.Probability.FiniteBankMoment
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitGridMaximum

@[expose] public section

/-! # Small geometric costs of cell-to-parent coefficient comparison -/
open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

/-- After choosing disorder, every cutoff normalization ratio costs an
arbitrarily small geometric power of the cutoff gap. -/
theorem exists_pair_ahom_ratio_bound (d : ℕ) {eta : ℝ} (heta : 0 < eta) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∀ j l : ℕ, l ≤ j →
        ahom M l / ahom M j ≤ (3 : ℝ) ^ (eta * ((j - l : ℕ) : ℝ)) := by
  let delta0 := Real.sqrt (eta * Real.log 3 / Real.log 2)
  have ha : 0 < eta * Real.log 3 / Real.log 2 := by
    exact div_pos (mul_pos heta (Real.log_pos (by norm_num))) (Real.log_pos (by norm_num))
  refine ⟨delta0, Real.sqrt_pos.mpr ha, ?_⟩
  intro M hM j l hlj
  have hdelta : M.delta ^ 2 ≤ eta * Real.log 3 / Real.log 2 := by
    have h := pow_le_pow_left₀ M.shellPrefix.delta_pos.le hM 2
    rwa [Real.sq_sqrt ha.le] at h
  have htau : 2 * tauSq M.P ≤ eta * Real.log 3 := by
    have h := tauSq_le_delta_sq M
    have h2 := mul_le_mul_of_nonneg_left hdelta (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    rw [mul_div_cancel₀ _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'] at h2
    linarith
  rcases hlj.eq_or_lt with h | h
  · subst j
    simp [div_self (ahom_pos M l).ne']
  · have hratio := (SubdiffusiveProcess.Providers.Section3.annealed_matrix_bounds.2 M j l h).2
    rw [div_le_iff₀ (ahom_pos M j)]
    refine hratio.trans (mul_le_mul_of_nonneg_right ?_ (ahom_pos M j).le)
    rw [Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.mpr
    have hg := mul_le_mul_of_nonneg_right htau (by positivity : (0 : ℝ) ≤ ((j - l : ℕ) : ℝ))
    nlinarith only [hg]

/-- Equal-order Holder multiplication for real random variables. -/
theorem pair_eLpNorm_mul_le {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (f g : Omega → ℝ) {q : ℝ} (hq : 0 < q)
    (hf : AEStronglyMeasurable f mu) (hg : AEStronglyMeasurable g mu) :
    eLpNorm (fun omega => f omega * g omega) (ENNReal.ofReal q) mu ≤
      eLpNorm f (ENNReal.ofReal (2 * q)) mu *
        eLpNorm g (ENNReal.ofReal (2 * q)) mu := by
  have htriple : Real.HolderTriple (2 * q) (2 * q) q :=
    ⟨by field_simp; ring, by positivity, by positivity⟩
  letI : ENNReal.HolderTriple (ENNReal.ofReal (2 * q)) (ENNReal.ofReal (2 * q))
      (ENNReal.ofReal q) := htriple.ennrealOfReal
  change eLpNorm (f • g) (ENNReal.ofReal q) mu ≤ _
  exact eLpNorm_smul_le_mul_eLpNorm (p := ENNReal.ofReal (2 * q))
    (q := ENNReal.ofReal (2 * q)) (r := ENNReal.ofReal q) hf hg

/-- The finite-bank cardinality-root estimate on an arbitrary finite carrier. -/
theorem pair_eLpNorm_finite_bank_le {Omega I : Type*} [MeasurableSpace Omega]
    [Fintype I] (mu : Measure Omega) {q : ℝ} (hq : 1 ≤ q)
    (F : I → Omega → ℝ) (hF : ∀ i, AEStronglyMeasurable (F i) mu)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ i, eLpNorm (F i) (ENNReal.ofReal q) mu ≤ ENNReal.ofReal C) :
    eLpNorm (fun omega => ‖fun i => F i omega‖) (ENNReal.ofReal q) mu ≤
      ENNReal.ofReal ((Fintype.card I : ℝ) ^ (1 / q) * C) := by
  classical
  let e := Fintype.equivFin I
  have h := SubdiffusiveProcess.eLpNorm_finite_bank_le mu
    (ENNReal.one_le_ofReal.mpr hq) ENNReal.ofReal_ne_top
    (fun i omega => F (e.symm i) omega) (fun i => hF (e.symm i))
    (ENNReal.ofReal C) (fun i => hbound (e.symm i))
  have heq : (fun omega => ‖fun i : Fin (Fintype.card I) => F (e.symm i) omega‖) =
      fun omega => ‖fun i : I => F i omega‖ := by
    funext omega
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro i
      exact norm_le_pi_norm (fun j : I => F j omega) (e.symm i)
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro i
      simpa using! norm_le_pi_norm (fun j : Fin (Fintype.card I) => F (e.symm j) omega) (e i)
  rw [heq, ENNReal.toReal_ofReal (zero_le_one.trans hq)] at h
  refine h.trans_eq ?_
  rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]

end SubdiffusiveProcess.Static
