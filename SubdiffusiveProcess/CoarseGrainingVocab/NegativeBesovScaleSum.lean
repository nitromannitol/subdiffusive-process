module

public import SubdiffusiveProcess.CoarseGrainingVocab.NegativeBesovOneCube

@[expose] public section

/-!
# Negative-Besov geometric scale sum

This module aggregates the descendant-block moment estimate over the exact-circ
diagonal and absorbs the one-cube growth into the negative-Besov scale weight.
-/

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open scoped BigOperators ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab
noncomputable section

/-- Raising the exact-circ diagonal to `p` removes its outer `p`-root. -/
theorem paperNegativeBesovCircDiagonal_rpow {d : ℕ} (Q : TriadicCube d) {s p : ℝ} (hp : 0 < p)
    (f : Vec d → ℝ) (hf : ExactCircIntegrable Q f) :
    (paperNegativeBesovCircDiagonal Q s p f hf) ^ p =
      ENNReal.ofReal s * ∑' j : ℕ, (exactCircDepthTerm Q s p f hf j) ^ p := by
  unfold paperNegativeBesovCircDiagonal
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one]
  rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one]

/-- A paper `L^p` bound controls the corresponding `p`-moment integral. -/
theorem paperLpNorm_lintegral_rpow_le {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {p b : ℝ} (hp : 0 < p) (X : Omega → ℝ)
    (hbound : paperLpNorm mu p X ≤ ENNReal.ofReal b) :
    ∫⁻ omega, ‖X omega‖ₑ ^ p ∂mu ≤ (ENNReal.ofReal b) ^ p := by
  have hpenn0 : ENNReal.ofReal p ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, hp.not_ge]
  have hpennTop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpow := ENNReal.rpow_le_rpow hbound hp.le
  unfold paperLpNorm at hpow
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral hpenn0 hpennTop] at hpow
  simp only [ENNReal.toReal_ofReal hp.le, one_div] at hpow
  rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one] at hpow
  exact hpow

/-- Raising an exact-circ depth term to `p` exposes its normalized block average. -/
theorem exactCircDepthTerm_rpow {d : ℕ} (Q : TriadicCube d) {s p : ℝ} (hp : 0 < p)
    (f : Vec d → ℝ) (hf : ExactCircIntegrable Q f) (j : ℕ) :
    (exactCircDepthTerm Q s p f hf j) ^ p =
      (exactCircDepthWeight Q s j) ^ p * exactCircDepthAverage Q p f hf j := by
  unfold exactCircDepthTerm
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one]

/-- Uniform block moments control one exact-circ depth term after descendant normalization. -/
theorem exactCircDepthTerm_moment_le_of_block {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (Q : TriadicCube d) {s p b : ℝ} (hp : 0 < p)
    (F : Omega → Vec d → ℝ) (hF : Measurable (Function.uncurry F))
    (hI : ∀ omega, ExactCircIntegrable Q (F omega)) (j : ℕ)
    (hblock : ∀ (R : TriadicCube d)
      (hR : R ∈ descendantsAtDepth Q j),
      paperLpNorm mu p (fun omega ↦
        exactCircBlockMean R (F omega) ((hI omega).block j R hR)) ≤
        ENNReal.ofReal b) :
    ∫⁻ omega, (exactCircDepthTerm Q s p (F omega) (hI omega) j) ^ p ∂mu ≤
      (exactCircDepthWeight Q s j * ENNReal.ofReal b) ^ p := by
  let D := descendantsAtDepth Q j
  have hDne : D.card ≠ 0 := (descendantsAtDepth_nonempty Q j).card_pos.ne'
  have hterm (omega : Omega) :
      (exactCircDepthTerm Q s p (F omega) (hI omega) j) ^ p =
        (exactCircDepthWeight Q s j) ^ p *
          ((D.card : ℝ≥0∞)⁻¹ * D.attach.sum fun R ↦
            (ENNReal.ofReal |exactCircBlockMean R.1 (F omega)
              ((hI omega).block j R.1 R.2)|) ^ p) := by
    rw [show (exactCircDepthTerm Q s p (F omega) (hI omega) j) ^ p =
      (exactCircDepthWeight Q s j) ^ p *
        exactCircDepthAverage Q p (F omega) (hI omega) j by
          unfold exactCircDepthTerm
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
          rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one]]
    rfl
  simp_rw [hterm]
  rw [lintegral_const_mul]
  · rw [lintegral_const_mul]
    · rw [lintegral_finset_sum]
      · have hsum : ∑ R ∈ D.attach,
            ∫⁻ omega, (ENNReal.ofReal |exactCircBlockMean R.1 (F omega)
              ((hI omega).block j R.1 R.2)|) ^ p ∂mu ≤
            D.card * (ENNReal.ofReal b) ^ p := by
          calc
            _ ≤ ∑ _R ∈ D.attach, (ENNReal.ofReal b) ^ p := by
              apply Finset.sum_le_sum
              intro R hR
              have hb := paperLpNorm_lintegral_rpow_le mu hp
                (fun omega ↦ exactCircBlockMean R.1 (F omega)
                  ((hI omega).block j R.1 R.2)) (hblock R.1 R.2)
              simpa only [← ofReal_norm_eq_enorm, Real.norm_eq_abs] using! hb
            _ = D.card * (ENNReal.ofReal b) ^ p := by simp
        calc
          (exactCircDepthWeight Q s j) ^ p *
              ((D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D.attach,
                ∫⁻ omega, (ENNReal.ofReal |exactCircBlockMean R.1 (F omega)
                  ((hI omega).block j R.1 R.2)|) ^ p ∂mu) ≤
            (exactCircDepthWeight Q s j) ^ p *
              ((D.card : ℝ≥0∞)⁻¹ *
                (D.card * (ENNReal.ofReal b) ^ p)) := by gcongr
          _ = (exactCircDepthWeight Q s j) ^ p * (ENNReal.ofReal b) ^ p := by
            have hc : ((D.card : ℝ≥0∞)⁻¹ *
                ((D.card : ℝ≥0∞) * (ENNReal.ofReal b) ^ p)) =
                (ENNReal.ofReal b) ^ p := by
              rw [← mul_assoc,
                ENNReal.inv_mul_cancel (by exact_mod_cast hDne) (by simp), one_mul]
            rw [hc]
          _ = (exactCircDepthWeight Q s j * ENNReal.ofReal b) ^ p := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
      · intro R hR
        exact ((measurable_exactCircBlockMean_of_uncurry R.1 F hF
          (fun omega ↦ (hI omega).block j R.1 R.2)).norm.ennreal_ofReal.pow_const p)
    · exact (Finset.measurable_sum _ fun R _ ↦
        (measurable_exactCircBlockMean_of_uncurry R.1 F hF
          (fun omega ↦ (hI omega).block j R.1 R.2)).norm.ennreal_ofReal.pow_const p)
  · exact (measurable_const.mul
      ((Finset.measurable_sum _ fun R _ ↦
        (measurable_exactCircBlockMean_of_uncurry R.1 F hF
          (fun omega ↦ (hI omega).block j R.1 R.2)).norm.ennreal_ofReal.pow_const p)))

/-- Tonelli aggregates uniform block moments over the complete exact-circ diagonal. -/
theorem paperNegativeBesovCircDiagonal_moment_le_of_block {d : ℕ}
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (Q : TriadicCube d) {s p : ℝ} (hp : 0 < p)
    (F : Omega → Vec d → ℝ) (hF : Measurable (Function.uncurry F))
    (hI : ∀ omega, ExactCircIntegrable Q (F omega)) (b : ℕ → ℝ)
    (hblock : ∀ (j : ℕ) (R : TriadicCube d)
      (hR : R ∈ descendantsAtDepth Q j),
      paperLpNorm mu p (fun omega ↦
        exactCircBlockMean R (F omega) ((hI omega).block j R hR)) ≤
        ENNReal.ofReal (b j)) :
    paperENNRealLpNorm mu p (fun omega ↦
        paperNegativeBesovCircDiagonal Q s p (F omega) (hI omega)) ≤
      (ENNReal.ofReal s) ^ p⁻¹ *
        (∑' j : ℕ, (exactCircDepthWeight Q s j * ENNReal.ofReal (b j)) ^ p) ^ p⁻¹ := by
  have hpoint (omega : Omega) :
      (paperNegativeBesovCircDiagonal Q s p (F omega) (hI omega)) ^ p =
        ENNReal.ofReal s * ∑' j : ℕ,
          (exactCircDepthTerm Q s p (F omega) (hI omega) j) ^ p := by
    unfold paperNegativeBesovCircDiagonal
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
    rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one]
    rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one]
  unfold paperENNRealLpNorm
  simp_rw [hpoint]
  rw [lintegral_const_mul]
  · rw [lintegral_tsum]
    · rw [← ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hp.le)]
      apply ENNReal.rpow_le_rpow _ (inv_nonneg.mpr hp.le)
      apply mul_le_mul_right
      apply ENNReal.tsum_le_tsum
      intro j
      exact exactCircDepthTerm_moment_le_of_block mu Q hp F hF hI j (hblock j)
    · intro j
      exact (measurable_exactCircDepthTerm_of_uncurry Q s p F hF hI j).pow_const p |>.aemeasurable
  · apply Measurable.ennreal_tsum
    intro j
    exact (measurable_exactCircDepthTerm_of_uncurry Q s p F hF hI j).pow_const p

/-- Dimension-free constant for the polynomially weighted geometric scale series. -/
noncomputable def negativeBesovScaleSeriesConst : ℝ :=
  (2 * Real.exp (Real.log 3 / 4) / (Real.log 3 / 2)) *
    ((1 + Real.log 3 / 2) / (Real.log 3 / 2)) ^ (2 : ℝ)⁻¹

/-- The exact scale series is summable and costs at most one inverse power of `s`. -/
theorem negativeBesov_scaleSeries_summable_and_le {s p : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hp : 2 ≤ p) :
    Summable (fun j : ℕ ↦
      (((1 + j : ℕ) : ℝ) * Real.exp (-(Real.log 3 / 2) * s * (j : ℝ))) ^ p) ∧
      (s * ∑' j : ℕ,
        (((1 + j : ℕ) : ℝ) * Real.exp (-(Real.log 3 / 2) * s * (j : ℝ))) ^ p) ^ p⁻¹ ≤
        negativeBesovScaleSeriesConst * s⁻¹ := by
  let k : ℝ := Real.log 3 / 2
  let D0 : ℝ := 2 * Real.exp (k / 2) / k
  let D1 : ℝ := (1 + k) / k
  let q : ℝ := Real.exp (-k * s)
  have hk : 0 < k := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hD0 : 0 < D0 := by dsimp [D0]; positivity
  have hD1 : 1 ≤ D1 := by
    dsimp [D1]
    rw [le_div_iff₀ hk]
    linarith
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hk hs])
  have hpoint (j : ℕ) :
      (((1 + j : ℕ) : ℝ) * Real.exp (-k * s * (j : ℝ))) ^ p ≤
        (D0 * s⁻¹) ^ p * q ^ j := by
    let x : ℝ := k * s * ((j : ℝ) + 1) / 2
    have hx0 : 0 ≤ x := by dsimp [x]; positivity
    have hxexp : x ≤ Real.exp x := by
      have := Real.add_one_le_exp x
      linarith
    have hjbound : ((1 + j : ℕ) : ℝ) ≤
        D0 * s⁻¹ * Real.exp (k * s * (j : ℝ) / 2) := by
      have hks : 0 < k * s := mul_pos hk hs
      have hraw := mul_le_mul_of_nonneg_left hxexp (by positivity : 0 ≤ 2 / (k * s))
      have he : Real.exp (k * s / 2) ≤ Real.exp (k / 2) := by
        apply Real.exp_le_exp.mpr
        have := mul_le_mul_of_nonneg_left hs1 hk.le
        linarith
      calc
        ((1 + j : ℕ) : ℝ) = 2 / (k * s) * x := by
          dsimp [x]
          push_cast
          field_simp [hks.ne']
          ring_nf
        _ ≤ 2 / (k * s) * Real.exp x := hraw
        _ = (2 / k) * s⁻¹ *
            (Real.exp (k * s / 2) * Real.exp (k * s * (j : ℝ) / 2)) := by
          rw [← Real.exp_add]
          dsimp [x]
          congr 1
          · field_simp [hk.ne', hs.ne']
          · ring_nf
        _ ≤ (2 / k) * s⁻¹ *
            (Real.exp (k / 2) * Real.exp (k * s * (j : ℝ) / 2)) := by
          gcongr
        _ = D0 * s⁻¹ * Real.exp (k * s * (j : ℝ) / 2) := by
          dsimp [D0]
          ring_nf
    have hseq : ((1 + j : ℕ) : ℝ) * Real.exp (-k * s * (j : ℝ)) ≤
        D0 * s⁻¹ * Real.exp (-k * s * (j : ℝ) / 2) := by
      calc
        _ ≤ (D0 * s⁻¹ * Real.exp (k * s * (j : ℝ) / 2)) *
            Real.exp (-k * s * (j : ℝ)) := by gcongr
        _ = D0 * s⁻¹ * Real.exp (-k * s * (j : ℝ) / 2) := by
          rw [show D0 * s⁻¹ * Real.exp (k * s * (j : ℝ) / 2) *
              Real.exp (-k * s * (j : ℝ)) =
              D0 * s⁻¹ * (Real.exp (k * s * (j : ℝ) / 2) *
                Real.exp (-k * s * (j : ℝ))) by ring_nf,
            ← Real.exp_add]
          ring_nf
    have hrpow := Real.rpow_le_rpow (by positivity) hseq (le_trans (by norm_num) hp)
    apply hrpow.trans
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
    have hexp : Real.exp (-k * s * (j : ℝ) / 2) ^ p ≤ q ^ j := by
      rw [← Real.exp_mul]
      dsimp [q]
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
      have ha0 : 0 ≤ k * s * (j : ℝ) :=
        mul_nonneg (mul_nonneg hk.le hs.le) hj0
      have hnonpos : -k * s * (j : ℝ) / 2 ≤ 0 := by nlinarith
      have hmul := mul_le_mul_of_nonpos_left hp hnonpos
      calc
        (-k * s * (j : ℝ) / 2) * p ≤
            (-k * s * (j : ℝ) / 2) * 2 := hmul
        _ = (j : ℝ) * (-k * s) := by ring_nf
    gcongr
  have hsummable : Summable (fun j : ℕ ↦
      (((1 + j : ℕ) : ℝ) * Real.exp (-k * s * (j : ℝ))) ^ p) := by
    have hqsum : Summable (fun j : ℕ ↦ q ^ j) :=
      summable_geometric_of_norm_lt_one (by
        simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using! hq1)
    have hright : Summable (fun j : ℕ ↦ (D0 * s⁻¹) ^ p * q ^ j) := by
      simpa only using! hqsum.mul_left ((D0 * s⁻¹) ^ p)
    exact hright.of_nonneg_of_le (fun _ ↦ by positivity) hpoint
  have hsum : ∑' j : ℕ,
      (((1 + j : ℕ) : ℝ) * Real.exp (-k * s * (j : ℝ))) ^ p ≤
      (D0 * s⁻¹) ^ p * (1 - q)⁻¹ := by
    have hqsum : Summable (fun j : ℕ ↦ q ^ j) :=
      summable_geometric_of_norm_lt_one (by
        simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using! hq1)
    have hright : Summable (fun j : ℕ ↦ (D0 * s⁻¹) ^ p * q ^ j) := by
      simpa only using! hqsum.mul_left ((D0 * s⁻¹) ^ p)
    calc
      _ ≤ ∑' j : ℕ, (D0 * s⁻¹) ^ p * q ^ j :=
        hsummable.tsum_le_tsum hpoint hright
      _ = (D0 * s⁻¹) ^ p * ∑' j : ℕ, q ^ j := by
        rw [← tsum_mul_left]
      _ = (D0 * s⁻¹) ^ p * (1 - q)⁻¹ := by
        rw [tsum_geometric_of_norm_lt_one (by
          simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using! hq1)]
  have hden : s * (1 - q)⁻¹ ≤ D1 := by
    let y : ℝ := k * s
    have hy : 0 < y := mul_pos hk hs
    have hqexp : q = Real.exp (-y) := by
      dsimp [q, y]
      congr 1
      ring_nf

    have hexpLower : 1 + y ≤ Real.exp y := by
      simpa [add_comm] using! Real.add_one_le_exp y
    have hqle : q ≤ (1 + y)⁻¹ := by
      rw [hqexp, Real.exp_neg]
      apply (inv_le_inv₀ (Real.exp_pos y) (by positivity : 0 < 1 + y)).2
      exact hexpLower
    have hdenLower : y / (1 + y) ≤ 1 - q := by
      calc
        y / (1 + y) = 1 - (1 + y)⁻¹ := by
          field_simp [ne_of_gt (by positivity : 0 < 1 + y)]
          ring_nf
        _ ≤ 1 - q := by linarith
    have hsfrac : s ≤ D1 * (y / (1 + y)) := by
      have hks : k * s ≤ k := mul_le_of_le_one_right hk.le hs1
      have hdenpos : 0 < 1 + k * s := by positivity
      rw [show D1 * (y / (1 + y)) =
          (1 + k) * s / (1 + k * s) by
        dsimp [D1, y]
        field_simp [hk.ne']]
      apply (le_div_iff₀ hdenpos).2
      nlinarith
    have hsden : s ≤ D1 * (1 - q) := by
      exact hsfrac.trans (mul_le_mul_of_nonneg_left hdenLower (by positivity))
    rw [show s * (1 - q)⁻¹ = s / (1 - q) by rw [div_eq_mul_inv]]
    exact (div_le_iff₀ (sub_pos.mpr hq1)).2 hsden
  have hprod :
      s * ∑' j : ℕ,
          (((1 + j : ℕ) : ℝ) * Real.exp (-k * s * (j : ℝ))) ^ p ≤
        D1 * (D0 * s⁻¹) ^ p := by
    calc
      _ ≤ s * ((D0 * s⁻¹) ^ p * (1 - q)⁻¹) :=
        mul_le_mul_of_nonneg_left hsum hs.le
      _ = (D0 * s⁻¹) ^ p * (s * (1 - q)⁻¹) := by ring_nf
      _ ≤ (D0 * s⁻¹) ^ p * D1 := by
        gcongr
      _ = D1 * (D0 * s⁻¹) ^ p := by ring_nf
  have hinvp : p⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp
  constructor
  · simpa only using! hsummable
  calc
    (s * ∑' j : ℕ,
        (((1 + j : ℕ) : ℝ) * Real.exp (-(Real.log 3 / 2) * s * (j : ℝ))) ^ p) ^ p⁻¹ =
      (s * ∑' j : ℕ,
        (((1 + j : ℕ) : ℝ) * Real.exp (-k * s * (j : ℝ))) ^ p) ^ p⁻¹ := by rfl
    _ ≤ (D1 * (D0 * s⁻¹) ^ p) ^ p⁻¹ :=
      Real.rpow_le_rpow (by positivity) hprod (inv_nonneg.mpr hp0.le)
    _ = D1 ^ p⁻¹ * ((D0 * s⁻¹) ^ p) ^ p⁻¹ := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
    _ = D1 ^ p⁻¹ * (D0 * s⁻¹) := by
      rw [← Real.rpow_mul (by positivity), mul_inv_cancel₀ hp0.ne', Real.rpow_one]
    _ ≤ D1 ^ (2 : ℝ)⁻¹ * (D0 * s⁻¹) := by
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hD1 hinvp) (by positivity)
    _ = negativeBesovScaleSeriesConst * s⁻¹ := by
      dsimp [negativeBesovScaleSeriesConst, D0, D1, k]
      ring_nf

/-- The outer origin-cube normalization cancels the absolute part of a depth weight. -/
theorem negativeBesov_exactCircDepthWeight_normalization {d m j : ℕ} {s : ℝ} :
    ENNReal.ofReal (Real.rpow 3 (-s * (m : ℝ))) *
        exactCircDepthWeight (originCube d (m : ℤ)) s j =
      ENNReal.ofReal (Real.exp (-(Real.log 3) * s * (j : ℝ))) := by
  have hrhs : Real.exp (-(Real.log 3) * s * (j : ℝ)) =
      Real.rpow 3 (-s * (j : ℝ)) := by
    calc
      _ = Real.exp (Real.log 3 * (-s * (j : ℝ))) := by
        congr 1
        ring_nf
      _ = Real.rpow 3 (-s * (j : ℝ)) :=
        (Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3) _).symm
  have hm := ENNReal.ofReal_rpow_of_pos
    (x := (3 : ℝ)) (p := -s * (m : ℝ)) (by norm_num : (0 : ℝ) < 3)
  have hj := ENNReal.ofReal_rpow_of_pos
    (x := (3 : ℝ)) (p := -s * (j : ℝ)) (by norm_num : (0 : ℝ) < 3)
  rw [hrhs]
  change ENNReal.ofReal ((3 : ℝ) ^ (-s * (m : ℝ))) *
      exactCircDepthWeight (originCube d (m : ℤ)) s j =
    ENNReal.ofReal ((3 : ℝ) ^ (-s * (j : ℝ)))
  rw [← hm, ← hj]
  norm_num only [ENNReal.ofReal_ofNat]
  unfold exactCircDepthWeight exactCircSourceDepth
  simp only [originCube]
  rw [← ENNReal.rpow_add]
  congr 1
  push_cast
  ring_nf
  all_goals norm_num

/-- `ENNReal` form of the normalized scale-series estimate. -/
theorem negativeBesov_ennreal_scaleSeries_le {A s p : ℝ} (hA : 0 ≤ A)
    (hs : 0 < s) (hs1 : s ≤ 1) (hp : 2 ≤ p) :
    (ENNReal.ofReal s) ^ p⁻¹ *
        (∑' j : ℕ, (ENNReal.ofReal
          (A * (((1 + j : ℕ) : ℝ) *
            Real.exp (-(Real.log 3 / 2) * s * (j : ℝ))))) ^ p) ^ p⁻¹ ≤
      ENNReal.ofReal (A * negativeBesovScaleSeriesConst * s⁻¹) := by
  let g : ℕ → ℝ := fun j ↦ ((1 + j : ℕ) : ℝ) *
    Real.exp (-(Real.log 3 / 2) * s * (j : ℝ))
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hg0 (j : ℕ) : 0 ≤ g j := by dsimp [g]; positivity
  obtain ⟨hgsum, hgseries⟩ := negativeBesov_scaleSeries_summable_and_le hs hs1 hp
  have hgsum' : Summable (fun j : ℕ ↦ (g j) ^ p) := by
    simpa only [g] using! hgsum
  have hAsum : Summable (fun j : ℕ ↦ (A * g j) ^ p) := by
    have hfactor : (fun j : ℕ ↦ (A * g j) ^ p) =
        fun j : ℕ ↦ A ^ p * (g j) ^ p := by
      funext j
      exact Real.mul_rpow hA (hg0 j)
    rw [hfactor]
    exact hgsum'.mul_left (A ^ p)
  have htsum : ENNReal.ofReal (∑' j : ℕ, (A * g j) ^ p) =
      ∑' j : ℕ, (ENNReal.ofReal (A * g j)) ^ p := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun j ↦ Real.rpow_nonneg _ _) hAsum]
    · apply congrArg tsum
      funext j
      exact (ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hA (hg0 j)) hp0.le).symm
    · intro j
      exact mul_nonneg hA (hg0 j)
  have hreal : (s * ∑' j : ℕ, (A * g j) ^ p) ^ p⁻¹ ≤
      A * negativeBesovScaleSeriesConst * s⁻¹ := by
    have hsumfactor : (∑' j : ℕ, (A * g j) ^ p) =
        A ^ p * ∑' j : ℕ, (g j) ^ p := by
      rw [show (fun j : ℕ ↦ (A * g j) ^ p) =
          fun j : ℕ ↦ A ^ p * (g j) ^ p by
        funext j
        exact Real.mul_rpow hA (hg0 j), tsum_mul_left]
    rw [hsumfactor]
    calc
      (s * (A ^ p * ∑' j : ℕ, (g j) ^ p)) ^ p⁻¹ =
          A * (s * ∑' j : ℕ, (g j) ^ p) ^ p⁻¹ := by
        rw [show s * (A ^ p * ∑' j : ℕ, (g j) ^ p) =
          A ^ p * (s * ∑' j : ℕ, (g j) ^ p) by ring_nf]
        rw [Real.mul_rpow (Real.rpow_nonneg _ _) (mul_nonneg hs.le
          (tsum_nonneg fun _ ↦ Real.rpow_nonneg _ _))]
        have hcancel : (A ^ p) ^ p⁻¹ = A := by
          rw [← Real.rpow_mul hA, mul_inv_cancel₀ hp0.ne', Real.rpow_one]
        rw [hcancel]
        all_goals
          first | exact hA | exact fun x ↦ hg0 x
      _ ≤ A * (negativeBesovScaleSeriesConst * s⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ hA
        simpa only [g] using! hgseries
      _ = A * negativeBesovScaleSeriesConst * s⁻¹ := by ring_nf
  calc
    _ = ENNReal.ofReal ((s * ∑' j : ℕ, (A * g j) ^ p) ^ p⁻¹) := by
      change (ENNReal.ofReal s) ^ p⁻¹ *
          (∑' j : ℕ, (ENNReal.ofReal (A * g j)) ^ p) ^ p⁻¹ = _
      rw [← ENNReal.ofReal_rpow_of_nonneg
        (mul_nonneg hs.le (tsum_nonneg fun _ ↦ Real.rpow_nonneg _ _))
        (inv_nonneg.mpr hp0.le)]
      rw [ENNReal.ofReal_mul hs.le, htsum]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hp0.le)]
      all_goals exact fun x ↦ mul_nonneg hA (hg0 x)
    _ ≤ ENNReal.ofReal (A * negativeBesovScaleSeriesConst * s⁻¹) :=
      ENNReal.ofReal_le_ofReal hreal

/-- Provider constant absorbing the one-cube and geometric-series constants. -/
noncomputable def negativeBesovScaleConst (d : ℕ) : ℝ :=
  1 + negativeBesovOneCubeConst d +
    2 * negativeBesovOneCubeConst d / Real.log 3 +
    negativeBesovOneCubeConst d * negativeBesovScaleSeriesConst

/-- Positivity of the geometric-series constant. -/
theorem negativeBesovScaleSeriesConst_pos : 0 < negativeBesovScaleSeriesConst := by
  unfold negativeBesovScaleSeriesConst
  have hk : 0 < Real.log 3 := Real.log_pos (by norm_num)
  positivity

/-- Positivity of the final scale-sum constant. -/
theorem negativeBesovScaleConst_pos (d : ℕ) : 0 < negativeBesovScaleConst d := by
  unfold negativeBesovScaleConst
  have hB := negativeBesovOneCubeConst_pos d
  have hK := negativeBesovScaleSeriesConst_pos
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  positivity

/-- Source Step 3 (`e.aL.Besov.sumscales`): the normalized exact-circ scale sum. -/
theorem negativeBesov_cutoffRatio_scaleSum_moment {d : ℕ} :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s p : ℝ),
        0 < s → s ≤ 1 → 2 ≤ p →
        C * p * M.delta ^ 2 ≤ s →
        p * M.delta ^ 2 * Real.log (2 + p) ≤ c →
        ∀ (m : ℕ) (n : ℤ), -1 ≤ n → n < (m : ℤ) →
          ENNReal.ofReal (Real.rpow 3 (-s * (m : ℝ))) *
              paperENNRealLpNorm M.P.toMeasure p
                (cutoffRatioNegativeBesov M m n s p) ≤
            ENNReal.ofReal (C * s⁻¹ * M.delta * Real.sqrt p * Real.log p) := by
  refine ⟨negativeBesovScaleConst d, negativeBesovOneCubeSmallConst d,
    negativeBesovScaleConst_pos d, negativeBesovOneCubeSmallConst_pos d, ?_⟩
  intro M s p hs hs1 hp hscale hsmall m n hn hnm
  let B := negativeBesovOneCubeConst d
  let C := negativeBesovScaleConst d
  let A := B * M.delta * Real.sqrt p * Real.log p
  let N := ENNReal.ofReal (Real.rpow 3 (-s * (m : ℝ)))
  let b : ℕ → ℝ := fun j ↦ A * (1 + j : ℕ) *
    Real.exp (B * p * M.delta ^ 2 * (j : ℝ))
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hB : 0 < B := negativeBesovOneCubeConst_pos d
  have hC : 0 < C := negativeBesovScaleConst_pos d
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hB.le M.shellPrefix.delta_pos.le) (Real.sqrt_nonneg p))
      (Real.log_nonneg (by linarith))
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have ht0 : 0 ≤ p * M.delta ^ 2 := mul_nonneg hp0.le (sq_nonneg _)
  have hcoef : 2 * B / Real.log 3 ≤ C := by
    dsimp [C, negativeBesovScaleConst]
    have hK := negativeBesovScaleSeriesConst_pos
    have htail : 0 ≤ B * negativeBesovScaleSeriesConst := mul_nonneg hB.le hK.le
    linarith
  have hraw : (2 * B / Real.log 3) * (p * M.delta ^ 2) ≤ s := by
    calc
      _ ≤ C * (p * M.delta ^ 2) := mul_le_mul_of_nonneg_right hcoef ht0
      _ = C * p * M.delta ^ 2 := by ring_nf
      _ ≤ s := hscale
  have hdecay : B * p * M.delta ^ 2 ≤ Real.log 3 / 2 * s := by
    calc
      _ = (Real.log 3 / 2) * ((2 * B / Real.log 3) * (p * M.delta ^ 2)) := by
        field_simp [hlog3.ne']
      _ ≤ (Real.log 3 / 2) * s :=
        mul_le_mul_of_nonneg_left hraw (by positivity)
  have hagg := paperNegativeBesovCircDiagonal_moment_le_of_block
    M.P.toMeasure (originCube d (m : ℤ)) (s := s) hp0
    (cutoffRatioMinusOne M m n) (measurable_cutoffRatioMinusOne_uncurry M m n)
    (cutoffRatioExactCircIntegrable M m n) b (by
      intro j R hR
      dsimp [b, A, B]
      exact negativeBesov_cutoffRatio_oneCube_moment M hp hsmall m n hn hnm j R hR)
  change paperENNRealLpNorm M.P.toMeasure p
      (cutoffRatioNegativeBesov M m n s p) ≤ _ at hagg
  have hpoint (j : ℕ) :
      N * exactCircDepthWeight (originCube d (m : ℤ)) s j *
          ENNReal.ofReal (b j) ≤
        ENNReal.ofReal (A * (((1 + j : ℕ) : ℝ) *
          Real.exp (-(Real.log 3 / 2) * s * (j : ℝ)))) := by
    rw [show N * exactCircDepthWeight (originCube d (m : ℤ)) s j =
        ENNReal.ofReal (Real.exp (-(Real.log 3) * s * (j : ℝ))) by
      exact negativeBesov_exactCircDepthWeight_normalization]
    rw [← ENNReal.ofReal_mul] <;> try positivity
    apply ENNReal.ofReal_le_ofReal
    dsimp [b]
    have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
    have hexp : Real.exp (-(Real.log 3) * s * (j : ℝ)) *
        Real.exp (B * p * M.delta ^ 2 * (j : ℝ)) ≤
        Real.exp (-(Real.log 3 / 2) * s * (j : ℝ)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right hdecay hj0
      nlinarith
    calc
      Real.exp (-(Real.log 3) * s * (j : ℝ)) *
          (A * ↑(1 + j) * Real.exp (B * p * M.delta ^ 2 * (j : ℝ))) =
        (A * ↑(1 + j)) *
          (Real.exp (-(Real.log 3) * s * (j : ℝ)) *
            Real.exp (B * p * M.delta ^ 2 * (j : ℝ))) := by ring_nf
      _ ≤ (A * ↑(1 + j)) *
          Real.exp (-(Real.log 3 / 2) * s * (j : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hexp (mul_nonneg hA (by positivity))
      _ = A * (↑(1 + j) *
          Real.exp (-(Real.log 3 / 2) * s * (j : ℝ))) := by ring_nf
  have hN0 : N ≠ 0 := by dsimp [N]; positivity
  have hNtop : N ≠ ⊤ := by dsimp [N]; exact ENNReal.ofReal_ne_top
  calc
    N * paperENNRealLpNorm M.P.toMeasure p
          (cutoffRatioNegativeBesov M m n s p) ≤
        N * ((ENNReal.ofReal s) ^ p⁻¹ *
          (∑' j : ℕ, (exactCircDepthWeight (originCube d (m : ℤ)) s j *
            ENNReal.ofReal (b j)) ^ p) ^ p⁻¹) := by gcongr
    _ = (ENNReal.ofReal s) ^ p⁻¹ *
        (∑' j : ℕ, (N * exactCircDepthWeight (originCube d (m : ℤ)) s j *
          ENNReal.ofReal (b j)) ^ p) ^ p⁻¹ := by
      rw [show N * ((ENNReal.ofReal s) ^ p⁻¹ *
          (∑' j : ℕ, (exactCircDepthWeight (originCube d (m : ℤ)) s j *
            ENNReal.ofReal (b j)) ^ p) ^ p⁻¹) =
        (ENNReal.ofReal s) ^ p⁻¹ *
          (N * (∑' j : ℕ, (exactCircDepthWeight (originCube d (m : ℤ)) s j *
            ENNReal.ofReal (b j)) ^ p) ^ p⁻¹) by ring_nf]
      congr 1
      have hNcancel : (N ^ p) ^ p⁻¹ = N := by
        rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one]
      calc
        N * (∑' j : ℕ, (exactCircDepthWeight (originCube d (m : ℤ)) s j *
            ENNReal.ofReal (b j)) ^ p) ^ p⁻¹ =
          (N ^ p) ^ p⁻¹ *
            (∑' j : ℕ, (exactCircDepthWeight (originCube d (m : ℤ)) s j *
              ENNReal.ofReal (b j)) ^ p) ^ p⁻¹ := by rw [hNcancel]
        _ = (N ^ p *
            ∑' j : ℕ, (exactCircDepthWeight (originCube d (m : ℤ)) s j *
              ENNReal.ofReal (b j)) ^ p) ^ p⁻¹ :=
          (ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hp0.le)).symm
        _ = (∑' j : ℕ, (N * exactCircDepthWeight (originCube d (m : ℤ)) s j *
            ENNReal.ofReal (b j)) ^ p) ^ p⁻¹ := by
          congr 1
          rw [← ENNReal.tsum_mul_left]
          apply congrArg tsum
          funext j
          rw [show N * exactCircDepthWeight (originCube d (m : ℤ)) s j *
              ENNReal.ofReal (b j) = N *
                (exactCircDepthWeight (originCube d (m : ℤ)) s j *
                  ENNReal.ofReal (b j)) by ring_nf,
            ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    _ ≤ (ENNReal.ofReal s) ^ p⁻¹ *
        (∑' j : ℕ, (ENNReal.ofReal
          (A * (((1 + j : ℕ) : ℝ) *
            Real.exp (-(Real.log 3 / 2) * s * (j : ℝ))))) ^ p) ^ p⁻¹ := by
      apply mul_le_mul_right
      apply ENNReal.rpow_le_rpow _ (inv_nonneg.mpr hp0.le)
      apply ENNReal.tsum_le_tsum
      intro j
      exact ENNReal.rpow_le_rpow (hpoint j) hp0.le
    _ ≤ ENNReal.ofReal (A * negativeBesovScaleSeriesConst * s⁻¹) :=
      negativeBesov_ennreal_scaleSeries_le hA hs hs1 hp
    _ ≤ ENNReal.ofReal (C * s⁻¹ * M.delta * Real.sqrt p * Real.log p) := by
      apply ENNReal.ofReal_le_ofReal
      dsimp [A, B, C]
      have hrest : negativeBesovOneCubeConst d * negativeBesovScaleSeriesConst ≤
          negativeBesovScaleConst d := by
        dsimp [negativeBesovScaleConst]
        have hdiv : 0 ≤ 2 * negativeBesovOneCubeConst d / Real.log 3 := by positivity
        linarith [negativeBesovOneCubeConst_pos d]
      have hfac : 0 ≤ s⁻¹ * M.delta * Real.sqrt p * Real.log p := by
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (inv_nonneg.mpr hs.le) M.shellPrefix.delta_pos.le)
            (Real.sqrt_nonneg p)) (Real.log_nonneg (by linarith))
      calc
        negativeBesovOneCubeConst d * M.delta * Real.sqrt p * Real.log p *
            negativeBesovScaleSeriesConst * s⁻¹ =
          (negativeBesovOneCubeConst d * negativeBesovScaleSeriesConst) *
            (s⁻¹ * M.delta * Real.sqrt p * Real.log p) := by ring_nf
        _ ≤ negativeBesovScaleConst d * (s⁻¹ * M.delta * Real.sqrt p * Real.log p) :=
          mul_le_mul_of_nonneg_right hrest hfac
        _ = negativeBesovScaleConst d * s⁻¹ * M.delta * Real.sqrt p * Real.log p := by ring_nf

end
end SubdiffusiveProcess.CoarseGrainingVocab
