module

public import SubdiffusiveProcess.PrefixTailNumerics
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.ErrorAverageClause
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.GoodScaleSaturation
public import SubdiffusiveProcess.CoarseGrainingVocab.OGammaToolkit
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_prefix_accumulated_error_tail_of_average
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (f : Ω → ℝ) (W lam b u A : ℝ) (hW : 0 < W) (hlam : 0 < lam)
    (hb : 0 < b) (hu : u ≤ lam / 8) (hbudget : A * b ^ 2 ≤ (lam / 8) ^ 2)
    (havg : SubdiffusiveProcess.OGammaLE P 2 (b / Real.sqrt W) (fun om => f om / W - u)) :
    P {om | lam * W / 4 < f om} ≤
      ENNReal.ofReal (2 * Real.exp (-(A * W))) := by
  have hsqrt : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW
  have hsub : {om | lam * W / 4 < f om} ⊆
      {om | lam / 8 ≤ f om / W - u} := by
    intro om hom
    have hf : lam / 4 < f om / W :=
      (lt_div_iff₀ hW).mpr (by simpa only [div_mul_eq_mul_div] using! hom)
    change lam / 8 ≤ f om / W - u
    linarith
  have hmarkov := SubdiffusiveProcess.CoarseGrainingVocab.OGamma.measureReal_ge_le_of_ogammaLE
    havg (div_pos hb hsqrt) (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ lam / 8)
  have hsquare : (((b / Real.sqrt W)⁻¹ * (lam / 8)) ^ (2 : ℝ)) =
      (lam / 8) ^ 2 * W / b ^ 2 := by
    rw [Real.rpow_two, inv_div]
    field_simp
    nlinarith [Real.sq_sqrt hW.le]
  have hexp : A * W ≤ (lam / 8) ^ 2 * W / b ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hb)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hbudget hW.le]
  have hr : P.real {om | lam * W / 4 < f om} ≤ 2 * Real.exp (-(A * W)) := by
    refine (measureReal_mono hsub (measure_ne_top _ _)).trans (hmarkov.trans ?_)
    rw [hsquare]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hexp)) (by norm_num)
  have := ENNReal.ofReal_le_ofReal hr
  simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using this

theorem prefix_accumulated_error_tail (d : ℕ) [NeZero d]
    (s lam A : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hlam : 0 < lam) (hA : 0 < A) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ delta0 →
      ∀ (n m : ℕ), n ≤ m → ∀ z : Vec d,
        (M.P.toMeasure {om | lam * ((m : ℝ) - (n : ℝ) + 1) / 4 <
            ∑ j ∈ Finset.Icc n m, accumulatedError M none j z s om} ≤
          ENNReal.ofReal (2 * Real.exp (-(A * ((m : ℝ) - (n : ℝ) + 1))))) ∧
        (M.P.toMeasure {om | lam * ((m : ℝ) - (n : ℝ) + 1) / 4 <
            ∑ j ∈ Finset.Icc n m, accumulatedError M none j z s om} ≤
          ENNReal.ofReal (1 / 2 : ℝ)) := by
  obtain ⟨C, hC, herror⟩ :=
    Section6CutoffRegularity.exists_cutoff_regularity_error_average_clause d
  let K : ℝ := C * s ^ (-7 / 2 : ℝ)
  let B : ℝ := max A (Real.log 4)
  have hK : 0 < K := mul_pos hC (Real.rpow_pos_of_pos hs.1 _)
  have hB : 0 < B := hA.trans_le (le_max_left _ _)
  let delta0 : ℝ := min (s / C)
    (min (lam / (8 * K)) ((lam / 8) ^ 2 / (B * K ^ 2)))
  have hd0 : 0 < delta0 :=
    lt_min (div_pos hs.1 hC)
      (lt_min (div_pos hlam (by positivity)) (div_pos (by positivity) (by positivity)))
  refine ⟨delta0, hd0, ?_⟩
  intro M hdelta n m hnm z
  have hd : 0 < M.delta := M.shellPrefix.delta_pos
  have hd1 : M.delta ≤ 1 := M.shellPrefix.delta_le_half.trans (by norm_num)
  have hlog : 0 < |Real.log M.delta| := abs_pos.mpr
    (Real.log_neg hd (M.shellPrefix.delta_le_half.trans_lt (by norm_num))).ne
  have hlogbudget := aux_prefix_accumulated_error_tail_log_budget hd hd1
  have hsmall : C * M.delta ^ 2 * |Real.log M.delta| ≤ s := by
    have hb : M.delta ≤ s / C := hdelta.trans (min_le_left _ _)
    have hc : M.delta * C ≤ s := (le_div_iff₀ hC).mp hb
    have := mul_le_mul_of_nonneg_left hlogbudget hC.le
    nlinarith
  have hmean : K * M.delta ≤ lam / 8 := by
    have hb : M.delta ≤ lam / (8 * K) :=
      hdelta.trans ((min_le_right _ _).trans (min_le_left _ _))
    have := (le_div_iff₀ (by positivity : 0 < 8 * K)).mp hb
    linarith
  have hrate : B * (K * M.delta * Real.sqrt |Real.log M.delta|) ^ 2 ≤
      (lam / 8) ^ 2 := by
    have hb : M.delta ≤ (lam / 8) ^ 2 / (B * K ^ 2) :=
      hdelta.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hdB := (le_div_iff₀ (by positivity : 0 < B * K ^ 2)).mp hb
    have hmono := mul_le_mul_of_nonneg_left hlogbudget
      (by positivity : 0 ≤ B * K ^ 2)
    rw [mul_pow, mul_pow, Real.sq_sqrt hlog.le]
    nlinarith
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hW : 0 < (m : ℝ) - (n : ℝ) + 1 := by linarith
  have hb : 0 < K * M.delta * Real.sqrt |Real.log M.delta| := by positivity
  have havg := herror M m s hs hsmall n m hnm z
  have heq : (fun om => (∑ j ∈ Finset.Icc n m,
      accumulatedError M (some m) j z s om) / ((m : ℝ) - (n : ℝ) + 1) -
        C * s ^ (-7 / 2 : ℝ) * M.delta) =
      (fun om => (∑ j ∈ Finset.Icc n m,
      accumulatedError M none j z s om) / ((m : ℝ) - (n : ℝ) + 1) -
        K * M.delta) := by
    funext om
    congr 2
    apply Finset.sum_congr rfl
    intro j hj
    exact Section6Cutoff.accumulatedError_some_eq_none_of_scale_le_cutoff
      M (Finset.mem_Icc.mp hj).2 z s om
  rw [heq] at havg
  have htail := aux_prefix_accumulated_error_tail_of_average M.P.toMeasure
    (fun om => ∑ j ∈ Finset.Icc n m, accumulatedError M none j z s om)
    ((m : ℝ) - (n : ℝ) + 1) lam (K * M.delta * Real.sqrt |Real.log M.delta|)
    (K * M.delta) B hW hlam hb hmean hrate havg
  constructor
  · refine htail.trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact Real.exp_le_exp.mpr (neg_le_neg
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hW.le))
  · refine htail.trans (ENNReal.ofReal_le_ofReal ?_)
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hBW : Real.log 4 ≤ B * ((m : ℝ) - (n : ℝ) + 1) := by
      have hB4 : Real.log 4 ≤ B := le_max_right _ _
      have hW1 : (1 : ℝ) ≤ (m : ℝ) - (n : ℝ) + 1 := by linarith
      exact hB4.trans (le_mul_of_one_le_right hB.le hW1)
    calc
      2 * Real.exp (-(B * ((m : ℝ) - (n : ℝ) + 1))) ≤
          2 * Real.exp (-Real.log 4) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hBW)) (by norm_num)
      _ = (1 / 2 : ℝ) := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num

end SubdiffusiveProcess.Paper
