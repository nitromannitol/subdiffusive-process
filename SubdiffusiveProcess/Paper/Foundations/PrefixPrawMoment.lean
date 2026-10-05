module

public import SubdiffusiveProcess.Paper.Foundations.PrefixPrawBank

@[expose] public section

/-!
# Cutoff-uniform `R`-th moments of the two `Psc` banks

For every real `R > 0`:
* `∫ Amaj^R ≤ card(bank) * (2 e^{R²σ²/4})^{card window}` with the bank cardinal depending
  only on the discount depth `j`;
* `∫ Bmaj^R ≤ (7^d * 2 e^{θ²σ²/4})^{9R/θ}` for every `θ > 6R`, independent of `m`, `j`, `z`.
-/

noncomputable section

open MeasureTheory _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.Paper

variable {d : ℕ}

/-- Layer independence for any family of layerwise observables. -/
theorem aux_prefix_praw_indep (M : GMCModel d) (G : ℕ → PotentialField d → ℝ≥0∞)
    (hG : ∀ i, Measurable (G i)) :
    ProbabilityTheory.iIndepFun (fun (i : ℕ) (omega : PotentialSample d) => G i (omega i))
      M.P.toMeasure :=
  M.shellPrefix.independent.comp G hG

/-- `R`-th moment of the product-window bank. -/
theorem aux_prefix_praw_Amaj_rpow_lintegral (M : GMCModel d) (m j : ℕ) (z : Vec d)
    (R : ℝ) :
    (∫⁻ omega : PotentialSample d, (aux_prefix_praw_Amaj m j z omega) ^ R ∂M.P.toMeasure) ≤
      ((aux_psf_cells d (m + 1 + j - (m - j))).card : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (R ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2) ^
          ((Finset.Icc (m - j) (m + j)).card) := by
  set cells := aux_psf_cells d (m + 1 + j - (m - j)) with hcells
  let S : (Fin d → ℕ) → PotentialSample d → ℝ := fun k omega =>
    ∑ i ∈ Finset.Icc (m - j) (m + j),
      aux_prefix_praw_obs (aux_prefix_praw_cellField i (aux_prefix_praw_Abase m j z k) omega)
  have hpt : ∀ omega : PotentialSample d, (aux_prefix_praw_Amaj m j z omega) ^ R ≤
      ∑ k ∈ cells, ENNReal.ofReal (Real.exp (R * S k omega)) := by
    intro omega
    obtain ⟨k0, hk0mem, hk0⟩ := cells.exists_mem_eq_sup' (aux_psf_cells_nonempty d _)
      (fun k => ENNReal.ofReal (Real.exp (S k omega)))
    have hrw : (aux_prefix_praw_Amaj m j z omega) ^ R =
        ENNReal.ofReal (Real.exp (R * S k0 omega)) := by
      have h1 : aux_prefix_praw_Amaj m j z omega = ENNReal.ofReal (Real.exp (S k0 omega)) := hk0
      rw [h1, aux_psf_ofReal_exp_rpow, mul_comm]
    rw [hrw]
    exact Finset.single_le_sum (f := fun k => ENNReal.ofReal (Real.exp (R * S k omega)))
      (fun k _ => zero_le) hk0mem
  have hterm : ∀ k : Fin d → ℕ,
      (∫⁻ omega, ENNReal.ofReal (Real.exp (R * S k omega)) ∂M.P.toMeasure) ≤
        (ENNReal.ofReal (Real.exp (R ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2) ^
          ((Finset.Icc (m - j) (m + j)).card) := by
    intro k
    let G : ℕ → PotentialField d → ℝ≥0∞ := fun i h =>
      ENNReal.ofReal (Real.exp (R * aux_prefix_praw_obs
        (_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale ((3 : ℝ) ^ i)
          (_root_.SubdiffusiveProcess.Model.PotentialField.translate (aux_prefix_praw_Abase m j z k) h))))
    have hG : ∀ i, Measurable (G i) := fun i =>
      (((aux_prefix_praw_obs_measurable.comp
        (aux_prefix_praw_translate_measurable i _)).const_mul _).exp).ennreal_ofReal
    have hsplit : ∀ omega : PotentialSample d,
        ENNReal.ofReal (Real.exp (R * S k omega)) =
          ∏ i ∈ Finset.Icc (m - j) (m + j), G i (omega i) := by
      intro omega
      rw [aux_psf_prod_ofReal_exp, Finset.mul_sum]
      rfl
    simp only [hsplit]
    rw [ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun _ _
      (aux_prefix_praw_indep M G hG)
      (fun i => (hG i).comp (measurable_potentialCoordinate (d := d) i))]
    calc
      ∏ i ∈ Finset.Icc (m - j) (m + j), ∫⁻ omega, G i (omega i) ∂M.P.toMeasure ≤
          ∏ _i ∈ Finset.Icc (m - j) (m + j),
            (ENNReal.ofReal (Real.exp (R ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2) :=
        Finset.prod_le_prod (fun i _ =>
          aux_prefix_praw_cell_exp_lin M i (aux_prefix_praw_Abase m j z k) R)
      _ = _ := by rw [Finset.prod_const]
  refine le_trans (lintegral_mono hpt) ?_
  rw [lintegral_finsetSum _ (fun k _ =>
    (((Finset.measurable_sum _ (fun i _ => aux_prefix_praw_cellObs_measurable i _)).const_mul
      _).exp).ennreal_ofReal)]
  calc
    ∑ k ∈ cells, ∫⁻ omega, ENNReal.ofReal (Real.exp (R * S k omega)) ∂M.P.toMeasure ≤
        ∑ _k ∈ cells, (ENNReal.ofReal (Real.exp (R ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2) ^
          ((Finset.Icc (m - j) (m + j)).card) := Finset.sum_le_sum (fun k _ => hterm k)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Linear exponential moment of one layer-adapted bank. -/
theorem aux_prefix_praw_bank_exp_lin (M : GMCModel d) (i n : ℕ) (z : Vec d) (lam : ℝ) :
    (∫⁻ omega : PotentialSample d, ENNReal.ofReal (Real.exp
      (lam * aux_prefix_praw_bank i n z omega)) ∂M.P.toMeasure) ≤
      ((aux_psf_cells d (n - i)).card : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (lam ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2) := by
  have h := aux_prefix_praw_sup_exp_lin M.P.toMeasure (aux_psf_cells d (n - i))
    (aux_psf_cells_nonempty d (n - i))
    (fun k omega => aux_prefix_praw_obs (aux_prefix_praw_cellField i
      (((3 : ℝ) ^ i) • aux_psf_center (n - i) (((3 : ℝ) ^ (-(i : ℤ))) • z) k) omega))
    (fun k => aux_prefix_praw_cellObs_measurable i _) lam _
    (fun k _ => aux_prefix_praw_cell_exp_lin M i _ lam)
  exact h

/-- Hölder form of the bank moment, with the tail cardinal bound `7^d`. -/
theorem aux_prefix_praw_bank_exp_holder (M : GMCModel d) (m j i : ℕ) (hi : m + j ≤ i)
    (z : Vec d) (lam theta : ℝ) (hlam : 0 < lam) (hlt : lam < theta) :
    (∫⁻ omega : PotentialSample d, ENNReal.ofReal (Real.exp
      (lam * aux_prefix_praw_bank i (m + 1 + j) z omega)) ∂M.P.toMeasure) ≤
      (((7 ^ d : ℕ) : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (theta ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2)) ^
          (lam / theta) := by
  have hth : 0 < theta := lt_trans hlam hlt
  refine (aux_prefix_praw_exp_holder M.P.toMeasure _
    (aux_prefix_praw_bank_measurable i (m + 1 + j) z) lam theta hlam hlt).trans ?_
  refine ENNReal.rpow_le_rpow ?_ (div_pos hlam hth).le
  refine (aux_prefix_praw_bank_exp_lin M i (m + 1 + j) z theta).trans ?_
  gcongr
  rw [aux_psf_cells_card]
  have hgap : m + 1 + j - i ≤ 1 := by omega
  have h3 : 2 * 3 ^ (m + 1 + j - i) + 1 ≤ 7 := by
    have : 3 ^ (m + 1 + j - i) ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hgap
    omega
  exact_mod_cast Nat.pow_le_pow_left h3 d

/-- Finite tail product moment, uniform in the cutoff, the depth and the centre. -/
theorem aux_prefix_praw_Btail_rpow_lintegral (M : GMCModel d) (m j K : ℕ) (z : Vec d)
    (R theta : ℝ) (hR : 0 < R) (hth : 6 * R < theta) :
    (∫⁻ omega : PotentialSample d, ENNReal.ofReal (Real.exp
        (R * ∑ i ∈ Finset.Icc (m + j) (m + j + K),
          aux_psf_lam m j i * aux_prefix_praw_bank i (m + 1 + j) z omega)) ∂M.P.toMeasure) ≤
      (((7 ^ d : ℕ) : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (theta ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2)) ^
          (9 * R / theta) := by
  have htheta : 0 < theta := by linarith
  set C : ℝ≥0∞ := ((7 ^ d : ℕ) : ℝ≥0∞) *
    (ENNReal.ofReal (Real.exp (theta ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2) with hC
  have hC1 : (1 : ℝ≥0∞) ≤ C := by
    have h7 : (1 : ℝ≥0∞) ≤ ((7 ^ d : ℕ) : ℝ≥0∞) := by
      exact_mod_cast Nat.one_le_pow d 7 (by norm_num)
    have hexp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (theta ^ 2 * aux_psf_sigma M ^ 2 / 4)) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (by positivity))
    have h2 : (1 : ℝ≥0∞) ≤
        ENNReal.ofReal (Real.exp (theta ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2 := by
      have := mul_le_mul' hexp (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      simpa using this
    have := mul_le_mul' h7 h2
    simpa [hC] using this
  have hC0 : C ≠ 0 := by
    intro h
    rw [h] at hC1
    exact absurd hC1 (by simp)
  have hCt : C ≠ ⊤ := by
    rw [hC]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num))
  let G : ℕ → PotentialField d → ℝ≥0∞ := fun i h =>
    ENNReal.ofReal (Real.exp ((R * aux_psf_lam m j i) *
      (aux_psf_cells d (m + 1 + j - i)).sup' (aux_psf_cells_nonempty d _)
        (fun k => aux_prefix_praw_obs (_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale ((3 : ℝ) ^ i)
          (_root_.SubdiffusiveProcess.Model.PotentialField.translate
            (((3 : ℝ) ^ i) • aux_psf_center (m + 1 + j - i) (((3 : ℝ) ^ (-(i : ℤ))) • z) k)
            h)))))
  have hG : ∀ i, Measurable (G i) := by
    intro i
    refine (((Measurable.const_mul ?_ _).exp).ennreal_ofReal)
    have h : Measurable ((aux_psf_cells d (m + 1 + j - i)).sup' (aux_psf_cells_nonempty d _)
        (fun k (h : PotentialField d) => aux_prefix_praw_obs
          (_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale ((3 : ℝ) ^ i) (_root_.SubdiffusiveProcess.Model.PotentialField.translate
            (((3 : ℝ) ^ i) • aux_psf_center (m + 1 + j - i) (((3 : ℝ) ^ (-(i : ℤ))) • z) k)
            h)))) :=
      Finset.measurable_sup' _ (fun k _ =>
        aux_prefix_praw_obs_measurable.comp (aux_prefix_praw_translate_measurable i _))
    convert h using 1
    funext h
    rw [Finset.sup'_apply]
  have hGbank : ∀ (i : ℕ) (omega : PotentialSample d), G i (omega i) =
      ENNReal.ofReal (Real.exp ((R * aux_psf_lam m j i) *
        aux_prefix_praw_bank i (m + 1 + j) z omega)) := fun _ _ => rfl
  have hsplit : ∀ omega : PotentialSample d,
      ENNReal.ofReal (Real.exp (R * ∑ i ∈ Finset.Icc (m + j) (m + j + K),
        aux_psf_lam m j i * aux_prefix_praw_bank i (m + 1 + j) z omega)) =
      ∏ i ∈ Finset.Icc (m + j) (m + j + K), G i (omega i) := by
    intro omega
    simp only [hGbank]
    rw [aux_psf_prod_ofReal_exp, Finset.mul_sum]
    congr 2
    exact Finset.sum_congr rfl (fun i _ => by ring)
  simp only [hsplit]
  rw [ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun _ _
    (aux_prefix_praw_indep M G hG)
    (fun i => (hG i).comp (measurable_potentialCoordinate (d := d) i))]
  calc
    ∏ i ∈ Finset.Icc (m + j) (m + j + K), ∫⁻ omega, G i (omega i) ∂M.P.toMeasure ≤
        ∏ i ∈ Finset.Icc (m + j) (m + j + K), C ^ ((R * aux_psf_lam m j i) / theta) := by
      refine Finset.prod_le_prod (fun i hi => ?_)
      have hi' : m + j ≤ i := (Finset.mem_Icc.1 hi).1
      simp only [hGbank]
      apply aux_prefix_praw_bank_exp_holder M m j i hi' z
      · exact mul_pos hR (aux_psf_lam_pos m j i)
      · have := aux_psf_lam_le_six m j i hi'
        nlinarith
    _ = C ^ (∑ i ∈ Finset.Icc (m + j) (m + j + K), (R * aux_psf_lam m j i) / theta) :=
      aux_psf_prod_rpow C hC0 hCt _ _
    _ ≤ C ^ (9 * R / theta) := by
      refine ENNReal.rpow_le_rpow_of_exponent_le hC1 ?_
      have hlam := aux_psf_lam_sum m j K
      calc
        ∑ i ∈ Finset.Icc (m + j) (m + j + K), (R * aux_psf_lam m j i) / theta =
            (R / theta) * ∑ i ∈ Finset.Icc (m + j) (m + j + K), aux_psf_lam m j i := by
          rw [Finset.mul_sum]; congr 1; ext i; ring
        _ ≤ (R / theta) * 9 := by gcongr
        _ = 9 * R / theta := by ring

/-- The infinite tail majorant: monotone convergence removes `K`. -/
theorem aux_prefix_praw_Bmaj_rpow_lintegral (M : GMCModel d) (m j : ℕ) (z : Vec d)
    (R theta : ℝ) (hR : 0 < R) (hth : 6 * R < theta) :
    (∫⁻ omega : PotentialSample d, (aux_prefix_praw_Bmaj m j z omega) ^ R ∂M.P.toMeasure) ≤
      (((7 ^ d : ℕ) : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (theta ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2)) ^
          (9 * R / theta) := by
  let f : ℕ → PotentialSample d → ℝ≥0∞ := fun K omega =>
    ENNReal.ofReal (Real.exp (∑ i ∈ Finset.Icc (m + j) (m + j + K),
      aux_psf_lam m j i * aux_prefix_praw_bank i (m + 1 + j) z omega))
  have hfmeas : ∀ K, Measurable (fun omega => (f K omega) ^ R) := by
    intro K
    exact ((Real.measurable_exp.comp (Finset.measurable_sum _ (fun i _ =>
      (aux_prefix_praw_bank_measurable i (m + 1 + j) z).const_mul _))).ennreal_ofReal).pow_const R
  have hfmono : Monotone f := by
    intro K K' hKK' omega
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (by omega)) ?_
    intro i _ _
    exact mul_nonneg (aux_psf_lam_pos m j i).le (aux_prefix_praw_bank_nonneg i _ z omega)
  have hpow : ∀ omega, (aux_prefix_praw_Bmaj m j z omega) ^ R = ⨆ K, (f K omega) ^ R := by
    intro omega
    have hsup : aux_prefix_praw_Bmaj m j z omega = ⨆ K, f K omega := rfl
    rw [hsup]
    apply le_antisymm
    · let Y : ℝ≥0∞ := ⨆ K, (f K omega) ^ R
      have hY : (⨆ K, f K omega) ≤ Y ^ (1 / R) := by
        refine iSup_le fun K => ?_
        have hK : (f K omega) ^ R ≤ Y := le_iSup (fun K : ℕ => (f K omega) ^ R) K
        have h := ENNReal.rpow_le_rpow hK (by positivity : 0 ≤ 1 / R)
        simpa only [← ENNReal.rpow_mul, mul_one_div_cancel hR.ne', ENNReal.rpow_one] using h
      have h := ENNReal.rpow_le_rpow hY hR.le
      simpa only [← ENNReal.rpow_mul, one_div_mul_cancel hR.ne', ENNReal.rpow_one] using h
    · exact iSup_le fun K => ENNReal.rpow_le_rpow (le_iSup (fun K : ℕ => f K omega) K) hR.le
  have hmono : Monotone (fun K omega => (f K omega) ^ R) := by
    intro K K' hKK' omega
    exact ENNReal.rpow_le_rpow (hfmono hKK' omega) hR.le
  simp_rw [hpow]
  rw [lintegral_iSup hfmeas hmono]
  refine iSup_le fun K => ?_
  have heq : ∀ omega, (f K omega) ^ R = ENNReal.ofReal (Real.exp
      (R * ∑ i ∈ Finset.Icc (m + j) (m + j + K),
        aux_psf_lam m j i * aux_prefix_praw_bank i (m + 1 + j) z omega)) := by
    intro omega
    simp only [f]
    rw [aux_psf_ofReal_exp_rpow, mul_comm]
  simp_rw [heq]
  exact aux_prefix_praw_Btail_rpow_lintegral M m j K z R theta hR hth

end SubdiffusiveProcess.Paper
