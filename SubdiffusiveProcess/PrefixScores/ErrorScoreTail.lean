import SubdiffusiveProcess.PrefixScores.ErrorBridge
import SubdiffusiveProcess.PrefixScores.Numerics
import SubdiffusiveProcess.Section6SumErrors.PaperAverage
import SubdiffusiveProcess.Section6SumErrors.PaperConstant

/-! Uniform exponential tails for the complete extended accumulated error. -/
open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Frozen.Assumptions
open Homogenization hiding Vec
open SubdiffusiveProcess SubdiffusiveProcess.PrefixScores
open SubdiffusiveProcess.Section6SumErrors.Response
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.PrefixScores

lemma exists_error_average_bound (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ M : GMCModel d, ∀ s : ℝ, 0 < s → s ≤ 1 →
      C * M.delta ^ 2 * |Real.log M.delta| ≤ s →
      ∀ n m : ℕ, n ≤ m → ∀ z : Vec d,
      ∫⁻ ω, ENNReal.ofReal (Real.exp
        (((C * s ^ (-7 / 2 : ℝ) * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ) *
          ((m : ℝ) - n + 1) ^ (-1 / 2 : ℝ))⁻¹ *
          max ((∑ k ∈ Finset.Icc n m, accumulatedError M none k z s ω) /
            ((m : ℝ) - n + 1) - C * s ^ (-7 / 2 : ℝ) * M.delta) 0) ^ (2 : ℕ))) ∂M.P.toMeasure ≤ 2 := by
  obtain ⟨D, hD, hrows⟩ := exists_uniformRow_bounds (d := d)
  obtain ⟨hC, hbudgetCoeff, htwo, hbase, hsq⟩ := paperConstant_bounds d D
  refine ⟨paperConstant d D, hC, ?_⟩
  intro M s hs hs1 hbudget n m hnm z
  have hfloor := floor_le_cutoff M hs hs1 hD hbudgetCoeff hbudget
  obtain ⟨hrow, hmean⟩ := hrows s hs hs1 M hfloor
  exact average_bound s hs hs1 M hD htwo hrow hmean hnm z

lemma exists_errorScore_tail (d : ℕ) [NeZero d] (s lam A : ℝ)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hlam : 0 < lam) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∀ z : Vec d, ∀ n k : ℕ,
        M.P.toMeasure {ω | ENNReal.ofReal (lam * (k : ℝ) / 4) <
          ∑ i ∈ Finset.range k, primitiveErrorScore M s ω (n + i) z} ≤
            ENNReal.ofReal (2 * Real.exp (-(A * (k : ℝ)))) := by
  obtain ⟨C, hC, hmoment⟩ := exists_error_average_bound d
  let H := C * s ^ (-7 / 2 : ℝ)
  let t := lam / 4
  let B := max A 0 + 1
  have hH : 0 < H := mul_pos hC (Real.rpow_pos_of_pos hs.1 _)
  have ht : 0 < t := by dsimp [t]; positivity
  have hB : 0 < B := by dsimp [B]; linarith [le_max_right A 0]
  have hAB : A ≤ B := by dsimp [B]; linarith [le_max_left A 0]
  let u1 := s / C
  let u2 := t / (2 * H)
  let u3 := t ^ 2 / (4 * H ^ 2 * B)
  have hu1 : 0 < u1 := div_pos hs.1 hC
  have hu2 : 0 < u2 := by dsimp [u2]; positivity
  have hu3 : 0 < u3 := by dsimp [u3]; positivity
  refine ⟨min 1 (min u1 (min u2 u3)), lt_min one_pos (lt_min hu1 (lt_min hu2 hu3)), ?_⟩
  intro M hdelta z n k
  have hd := M.shellPrefix.delta_pos
  have hd1 : M.delta ≤ 1 := hdelta.trans (min_le_left _ _)
  have hdlog := delta_sq_log_le_self hd hd1
  have hdu1 : M.delta ≤ u1 := hdelta.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdu2 : M.delta ≤ u2 := hdelta.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hdu3 : M.delta ≤ u3 := hdelta.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hbudget : C * M.delta ^ 2 * |Real.log M.delta| ≤ s := by
    calc
      _ = C * (M.delta ^ 2 * |Real.log M.delta|) := by ring
      _ ≤ C * u1 := mul_le_mul_of_nonneg_left (hdlog.trans hdu1) hC.le
      _ = s := by dsimp [u1]; field_simp
  have hmean : H * M.delta ≤ t / 2 := by
    calc
      _ ≤ H * u2 := mul_le_mul_of_nonneg_left hdu2 hH.le
      _ = t / 2 := by dsimp [u2]; field_simp
  have hvar : H ^ 2 * (M.delta ^ 2 * |Real.log M.delta|) * B ≤ (t / 2) ^ 2 := by
    calc
      _ ≤ H ^ 2 * u3 * B := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hdlog.trans hdu3) (sq_nonneg H)) hB.le
      _ = (t / 2) ^ 2 := by dsimp [u3]; field_simp; ring
  by_cases hk : k = 0
  · subst k
    simp
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  let m := n + (k - 1)
  let W : ℝ := k
  have hW : 0 < W := by dsimp [W]; exact_mod_cast hkpos
  have hnm : n ≤ m := Nat.le_add_right n (k - 1)
  have hlen : (m : ℝ) - n + 1 = W := by
    dsimp [m, W]
    rw [Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    ring
  let X : PotentialSample d → ℝ := fun ω => ∑ j ∈ Finset.Icc n m, accumulatedError M none j z s ω
  have hX : Measurable X := Finset.measurable_sum _ (fun j _ =>
    Section6CutoffRegularity.measurable_accumulatedError M none j z s)
  let b := H * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ) * W ^ (-1 / 2 : ℝ)
  have hlog : 0 < |Real.log M.delta| := abs_pos.mpr (Real.log_neg hd
    (M.shellPrefix.delta_le_half.trans_lt (by norm_num))).ne
  have hb : 0 < b := by dsimp [b]; positivity
  have hbEq : b = H * M.delta * Real.sqrt |Real.log M.delta| / Real.sqrt W := by
    dsimp [b]
    rw [← Real.sqrt_eq_rpow, show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
      Real.rpow_neg hW.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
  have hbSq : b ^ 2 * W = H ^ 2 * (M.delta ^ 2 * |Real.log M.delta|) := by
    rw [hbEq, div_pow]
    rw [Real.sq_sqrt hW.le, mul_pow, mul_pow, Real.sq_sqrt hlog.le]
    field_simp
  have hbBudget : b ^ 2 * (B * W) ≤ (t / 2) ^ 2 := by
    rw [show b ^ 2 * (B * W) = (b ^ 2 * W) * B by ring, hbSq]
    exact hvar
  have hm : ∫⁻ ω, ENNReal.ofReal (Real.exp ((b⁻¹ * max (X ω / W - H * M.delta) 0) ^ (2 : ℕ))) ∂M.P.toMeasure ≤ 2 := by
    have h := hmoment M s hs.1 hs.2 hbudget n m hnm z
    simpa only [H, X, b, hlen] using h
  have htail := squareAverage_tail M.P.toMeasure X hX (H * M.delta) b t B W hb hW ht hmean hbBudget hm
  have hsub : ∀ᵐ ω ∂M.P.toMeasure,
      ω ∈ {ω | ENNReal.ofReal (lam * (k : ℝ) / 4) <
        ∑ i ∈ Finset.range k, primitiveErrorScore M s ω (n + i) z} →
      ω ∈ {ω | t * W < X ω} := by
    have heq : ∀ᵐ ω ∂M.P.toMeasure, ∀ j : ℕ,
        primitiveErrorScore M s ω j z = ENNReal.ofReal (accumulatedError M none j z s ω) :=
      ae_all_iff.mpr (fun j => ae_errorScore_eq M s j z)
    filter_upwards [heq] with ω hω
    intro hω'
    have hnonneg : ∀ j : ℕ, 0 ≤ accumulatedError M none j z s ω := by
      intro j
      unfold accumulatedError
      apply add_nonneg
      · apply add_nonneg
        · apply add_nonneg
          · apply Real.sSup_nonneg
            rintro r ⟨a, l, ha, hl, x, hg, hx, rfl⟩; positivity
          · apply Real.sSup_nonneg
            rintro r ⟨a, ha, rfl⟩
            exact mul_nonneg (by positivity) (Section6CutoffRegularity.supNormOn_nonneg' _ _)
        · exact mul_nonneg (by positivity) (Section6CutoffRegularity.supNormOn_nonneg' _ _)
      · apply tsum_nonneg
        intro l
        split_ifs with hl
        · exact mul_nonneg (by positivity) (vectorSupNormOn_shellGradient_nonneg l j hl z ω)
        · exact le_refl 0
    simp_rw [hω] at hω'
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hnonneg (n + i))] at hω'
    have hreal := (ENNReal.ofReal_lt_ofReal_iff'.mp hω').1
    rw [sum_window (fun j => accumulatedError M none j z s ω) n k hkpos] at hreal
    simpa only [t, W, X, m, div_mul_eq_mul_div] using hreal
  calc
    _ ≤ M.P.toMeasure {ω | t * W < X ω} := measure_mono_ae hsub
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(B * W))) := htail
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(A * (k : ℝ)))) := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hAB hW.le))

end SubdiffusiveProcess.PrefixScores
