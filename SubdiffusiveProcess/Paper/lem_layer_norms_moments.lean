import Mathlib
import SubdiffusiveProcess.Paper.lem_layer_norms_peeling
import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Paper

open Homogenization Homogenization.IndependentSums

private theorem aux_tail_to_isBigO
    {Om : Type} [MeasurableSpace Om] (P : Measure Om) [IsProbabilityMeasure P]
    (X : Om → ℝ) (A D : ℝ) (hA : 0 < A) (hD : 0 < D)
    (hAD : A ^ 2 = D)
    (hX0 : ∀ omega, 0 ≤ X omega)
    (htail : ∀ s : ℝ, 0 ≤ s →
      P {omega | s < X omega} ≤ ENNReal.ofReal (Real.exp (-(s ^ 2 / D)))) :
    IsBigO P (gammaSigma 2) X A := by
  rw [isBigO_gammaSigma_iff]
  intro t ht
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have hAt0 : 0 ≤ A * t := mul_nonneg hA.le ht0
  have htail' := htail (A * t) hAt0
  have hden : (A * t) ^ 2 / D = t ^ 2 := by
    rw [mul_pow, hAD]
    field_simp [hD.ne']
  have hmeasure : P {omega | A * t < X omega} ≤ ENNReal.ofReal (Real.exp (-t ^ 2)) := by
    simpa [hden] using htail'
  have hmeasureReal :
      (P {omega | A * t < X omega}).toReal ≤ Real.exp (-t ^ 2) := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure).trans_eq
      (ENNReal.toReal_ofReal (Real.exp_pos _).le)
  have hset : absTailEvent X (A * t) = {omega | A * t < X omega} := by
    ext omega
    simp [absTailEvent, upperTailEvent, abs_of_nonneg (hX0 omega)]
  rw [hset]
  simpa [measureReal_def, Real.rpow_two] using hmeasureReal

private theorem aux_eLpNorm_le_of_exp_bound
    {Om : Type} [MeasurableSpace Om] (P : Measure Om) [IsProbabilityMeasure P]
    {p B c R : ℝ} {Y X : Om → ℝ}
    (hp : 0 < p) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hY0 : ∀ omega, 0 ≤ Y omega)
    (hpoint : ∀ omega, Y omega ^ p ≤ B * Real.exp (c * X omega))
    (hExp : Integrable (fun omega => Real.exp (c * X omega)) P)
    (hInt : B * (∫ omega, Real.exp (c * X omega) ∂P) ≤ R ^ p) :
    eLpNorm Y (ENNReal.ofReal p) P ≤ ENNReal.ofReal R := by
  have hp0 : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  have hlin :
      (∫⁻ omega, ‖Y omega‖ₑ ^ (ENNReal.ofReal p).toReal ∂P) ≤
        ENNReal.ofReal (B * (∫ omega, Real.exp (c * X omega) ∂P)) := by
    calc
      (∫⁻ omega, ‖Y omega‖ₑ ^ (ENNReal.ofReal p).toReal ∂P) ≤
          ∫⁻ omega, ENNReal.ofReal (B * Real.exp (c * X omega)) ∂P := by
            refine lintegral_mono (fun omega => ?_)
            rw [hp0, Real.enorm_eq_ofReal (hY0 omega),
              ENNReal.ofReal_rpow_of_nonneg (hY0 omega) hp.le]
            exact ENNReal.ofReal_le_ofReal (hpoint omega)
      _ = ENNReal.ofReal (B * (∫ omega, Real.exp (c * X omega) ∂P)) := by
        symm
        rw [← integral_const_mul]
        exact ofReal_integral_eq_lintegral_ofReal (hExp.const_mul B)
          (ae_of_all _ (fun omega => mul_nonneg hB (Real.exp_nonneg _)))
  rw [eLpNorm_eq_lintegral_rpow_enorm (ENNReal.ofReal_pos.mpr hp).ne'
    ENNReal.ofReal_ne_top]
  calc
    (∫⁻ omega, ‖Y omega‖ₑ ^ (ENNReal.ofReal p).toReal ∂P) ^
          (1 / (ENNReal.ofReal p).toReal) ≤
        (ENNReal.ofReal (B * (∫ omega, Real.exp (c * X omega) ∂P))) ^
          (1 / (ENNReal.ofReal p).toReal) :=
      ENNReal.rpow_le_rpow hlin (by positivity)
    _ ≤ (ENNReal.ofReal (R ^ p)) ^ (1 / p) := by
      rw [hp0]
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hInt) (one_div_nonneg.mpr hp.le)
    _ = ENNReal.ofReal R := by
      rw [← ENNReal.ofReal_rpow_of_nonneg hR hp.le]
      rw [← ENNReal.rpow_mul]
      have hpne : p ≠ 0 := ne_of_gt hp
      field_simp
      simp

private theorem aux_rpow_add_le
    {a x q : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (hq : 0 ≤ q) :
    (a + x) ^ q ≤ 2 ^ q * (a ^ q + x ^ q) := by
  have hsum : a + x ≤ 2 * max a x := by
    by_cases hax : a ≤ x
    · rw [max_eq_right hax]
      linarith
    · rw [max_eq_left (le_of_not_ge hax)]
      linarith
  calc
    (a + x) ^ q ≤ (2 * max a x) ^ q := Real.rpow_le_rpow (by positivity) hsum hq
    _ = 2 ^ q * (max a x) ^ q := by
      have hmax : 0 ≤ max a x := le_trans ha (le_max_left _ _)
      rw [Real.mul_rpow (by positivity) hmax]
    _ = 2 ^ q * max (a ^ q) (x ^ q) := by rw [Real.rpow_max ha hx hq]
    _ ≤ 2 ^ q * (a ^ q + x ^ q) := by
      gcongr
      exact max_le (le_add_of_nonneg_right (Real.rpow_nonneg hx q))
        (le_add_of_nonneg_left (Real.rpow_nonneg ha q))

private theorem aux_log_cover_bound
    (d : ℕ) (Cc : ℝ) (hCc : 1 ≤ Cc) (cover r : ℝ)
    (hcover : 1 ≤ cover) (hr : 0 < r) (hrle : r ≤ 1)
    (hupper : cover ≤ Cc * r ^ (-(d : ℝ))) :
    Real.log (2 * cover) ≤
      (Real.log (2 * Cc) + (d : ℝ) + 1) * (1 + |Real.log r|) := by
  have hcover_pos : 0 < cover := lt_of_lt_of_le zero_lt_one hcover
  have hCc_pos : 0 < Cc := lt_of_lt_of_le zero_lt_one hCc
  have hupper_pos : 0 < Cc * r ^ (-(d : ℝ)) :=
    mul_pos hCc_pos (Real.rpow_pos_of_pos hr _)
  have hlog_le : Real.log cover ≤ Real.log Cc - (d : ℝ) * Real.log r := by
    have h := Real.log_le_log hcover_pos hupper
    rw [Real.log_mul hCc_pos.ne' (Real.rpow_pos_of_pos hr _).ne',
      Real.log_rpow hr] at h
    simpa [sub_eq_add_neg] using h
  have hlog_r_nonpos : Real.log r ≤ 0 := Real.log_nonpos (le_of_lt hr) hrle
  have hlog_two_cover :
      Real.log (2 * cover) ≤ Real.log (2 * Cc) + (d : ℝ) * |Real.log r| := by
    calc
      Real.log (2 * cover) = Real.log 2 + Real.log cover := by
        rw [Real.log_mul (by norm_num) hcover_pos.ne']
      _ ≤ Real.log 2 + (Real.log Cc - (d : ℝ) * Real.log r) :=
        by simpa [add_comm] using add_le_add_left hlog_le (Real.log 2)
      _ = Real.log (2 * Cc) + (d : ℝ) * |Real.log r| := by
        rw [Real.log_mul (by norm_num) hCc_pos.ne', abs_of_nonpos hlog_r_nonpos]
        ring
  have hlog_twoCc : 0 ≤ Real.log (2 * Cc) :=
    Real.log_nonneg (by nlinarith)
  have hd : 0 ≤ (d : ℝ) := by positivity
  have hy : 0 ≤ |Real.log r| := abs_nonneg _
  have hL : 0 ≤ 1 + |Real.log r| := by linarith
  have hprod :
      Real.log (2 * Cc) + (d : ℝ) * |Real.log r| ≤
        (Real.log (2 * Cc) + (d : ℝ) + 1) * (1 + |Real.log r|) := by
    nlinarith [mul_nonneg hlog_twoCc hy, mul_nonneg hd hy]
  exact hlog_two_cover.trans hprod



theorem lem_layer_norms_moments :
    ∀ (d : ℕ) (hd : 1 ≤ d) (Cc : ℝ) (hCc : 1 ≤ Cc),
    ∃ C0 : ℝ, 0 < C0 ∧
    ∀ p : ℝ, 0 < p → ∃ Cp : ℝ, 0 < Cp ∧
    ∀ k lam : ℝ, 0 ≤ k → 0 ≤ lam → ∃ Cpk : ℝ, 0 < Cpk ∧
    ∀ (Om : Type) [MeasurableSpace Om] (P : Measure Om) [IsProbabilityMeasure P],
    ∀ disorder : ℝ, 0 < disorder → disorder ≤ 1 →
    ∀ S : ℕ → Om → ℝ,
    (∀ j, AEStronglyMeasurable (S j) P) →
    (∀ j omega, 0 ≤ S j omega) →
    ∀ covers : ℕ → ℝ,
    (∀ j, 1 ≤ covers j) →
    (∀ j, covers j ≤ Cc * ((3 : ℝ) ^ (-(j : ℝ))) ^ (-(d : ℝ))) →
    (∀ j : ℕ,
      let a := disorder * Real.sqrt (Cc * Real.log (2 * covers j))
      let X := fun omega => max (S j omega - a) 0
      ∀ s : ℝ, 0 ≤ s → P {omega | s < X omega} ≤
        ENNReal.ofReal (Real.exp (-(s ^ 2 / (Cc * disorder ^ 2))))) →
    ∀ j : ℕ,
      let r := (3 : ℝ) ^ (-(j : ℝ))
      eLpNorm (fun omega => (S j omega) ^ k * Real.exp (lam * S j omega))
        (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (Cpk * disorder ^ k * (1 + abs (Real.log r)) ^ (k / 2) *
          Real.exp (C0 * lam * disorder * Real.sqrt (1 + abs (Real.log r)) +
            Cp * lam ^ 2 * disorder ^ 2)) := by
  intro d hd Cc hCc
  let H : ℝ := Real.log (2 * Cc) + (d : ℝ) + 1
  have hH : 0 < H := by
    dsimp [H]
    have hlog : 0 ≤ Real.log (2 * Cc) := Real.log_nonneg (by nlinarith)
    have hd' : 0 ≤ (d : ℝ) := by positivity
    linarith
  let K : ℝ := Real.sqrt (Cc * H)
  have hK : 0 < K := by
    dsimp [K]
    exact Real.sqrt_pos.mpr (mul_pos (lt_of_lt_of_le zero_lt_one hCc) hH)
  refine ⟨K + Real.sqrt Cc + 1, by positivity, ?_⟩
  intro p hp
  let Cp : ℝ := p * Cc / 2 + 1
  have hCp : 0 < Cp := by
    dsimp [Cp]
    have : 0 < p * Cc := mul_pos hp (lt_of_lt_of_le zero_lt_one hCc)
    linarith
  refine ⟨Cp, hCp, ?_⟩
  intro k lam hk hlam
  let q : ℝ := k * p
  let theta : ℝ := lam * p
  let M : ℝ := 2 ^ q * (K ^ q + (q * Real.sqrt Cc) ^ q)
  let Cpk : ℝ := (4 * M * Real.exp (1 / 2 : ℝ)) ^ (1 / p)
  have hq : 0 ≤ q := mul_nonneg hk hp.le
  have htheta : 0 ≤ theta := mul_nonneg hlam hp.le
  have hM : 0 < M := by
    dsimp [M]
    have htwo : 0 < (2 : ℝ) ^ q := Real.rpow_pos_of_pos (by norm_num) _
    have hKq : 0 < K ^ q := Real.rpow_pos_of_pos hK _
    have hsum : 0 < K ^ q + (q * Real.sqrt Cc) ^ q :=
      lt_of_lt_of_le hKq (le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _))
    exact mul_pos htwo hsum
  have hCpk : 0 < Cpk := by
    dsimp [Cpk]
    exact Real.rpow_pos_of_pos (mul_pos (mul_pos (by norm_num) hM) (Real.exp_pos _)) _
  refine ⟨Cpk, hCpk, ?_⟩
  intro Om _ P _ disorder hdis hdisle S hSmeas hS0 covers hcover hcover_upper htail j
  let r : ℝ := (3 : ℝ) ^ (-(j : ℝ))
  let L : ℝ := 1 + |Real.log r|
  let cov : ℝ := covers j
  let a : ℝ := disorder * Real.sqrt (Cc * Real.log (2 * cov))
  let X : Om → ℝ := fun omega => max (S j omega - a) 0
  let A : ℝ := disorder * Real.sqrt Cc
  have hrpos : 0 < r := by
    dsimp [r]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hrle : r ≤ 1 := by
    dsimp [r]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (neg_nonpos.mpr (by positivity))
  have hlog := aux_log_cover_bound d Cc hCc (covers j) r (hcover j) hrpos hrle
    (hcover_upper j)
  have hlog0 : 0 ≤ Real.log (2 * cov) := by
    dsimp [cov]
    exact Real.log_nonneg (by nlinarith [hcover j])
  have hL : 0 < L := by
    dsimp [L]
    linarith [abs_nonneg (Real.log r)]
  have hCc0 : 0 ≤ Cc := le_trans zero_le_one hCc
  have hKscale :
      Real.sqrt (Cc * Real.log (2 * cov)) ≤ K * Real.sqrt L := by
    have hinside : Cc * Real.log (2 * cov) ≤ Cc * (H * L) := by
      dsimp [L]
      exact mul_le_mul_of_nonneg_left (by simpa [H] using hlog) hCc0
    have hsqrt := Real.sqrt_le_sqrt hinside
    have heq : Real.sqrt (Cc * (H * L)) = K * Real.sqrt L := by
      dsimp [K]
      rw [show Cc * (H * L) = (Cc * H) * L by ring, Real.sqrt_mul (by positivity)]
    rw [heq] at hsqrt
    exact hsqrt
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg hdis.le (Real.sqrt_nonneg _)
  have ha_scale : a ≤ disorder * K * Real.sqrt L := by
    dsimp [a]
    exact (mul_le_mul_of_nonneg_left hKscale hdis.le).trans_eq (by ring)
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos hdis (Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hCc))
  have hAD : A ^ 2 = Cc * disorder ^ 2 := by
    dsimp [A]
    rw [mul_pow, Real.sq_sqrt hCc0]
    ring
  have hX0 : ∀ omega, 0 ≤ X omega := by
    intro omega
    exact le_max_right _ _
  have hXmeas : AEMeasurable X P := by
    dsimp [X]
    exact (hSmeas j).aemeasurable.sub_const a |>.max (aemeasurable_const)
  have hbigX : IsBigO P (gammaSigma 2) X A := by
    apply aux_tail_to_isBigO P X A (Cc * disorder ^ 2) hA
      (mul_pos (lt_of_lt_of_le zero_lt_one hCc) (sq_pos_of_pos hdis)) hAD hX0
    intro s hs
    simpa [X, A, a, cov] using (htail j s hs)
  have hSX : ∀ omega, S j omega ≤ a + X omega := by
    intro omega
    have hm := le_max_left (S j omega - a) 0
    dsimp [X]
    linarith
  have hXq : ∀ omega, X omega ^ q ≤ (q * A) ^ q * Real.exp (X omega / A) := by
    intro omega
    have hh := ProbabilityTheory.rpow_abs_le_mul_exp_abs (X omega)
      hq (t := A⁻¹) (inv_ne_zero hA.ne')
    have hqa : q / |A⁻¹| = q * A := by
      rw [abs_of_pos (inv_pos.mpr hA)]
      field_simp
    have he : |A⁻¹| * X omega = X omega / A := by
      rw [abs_of_pos (inv_pos.mpr hA)]
      field_simp
    rw [abs_of_nonneg (hX0 omega), hqa, he] at hh
    exact hh
  let B : ℝ := 2 ^ q * (a ^ q + (q * A) ^ q) * Real.exp (theta * a)
  let c : ℝ := theta + A⁻¹
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hc : 0 ≤ c := by
    dsimp [c]
    exact add_nonneg htheta (inv_nonneg.mpr hA.le)
  have hpoint : ∀ omega,
      (S j omega ^ k * Real.exp (lam * S j omega)) ^ p ≤
        B * Real.exp (c * X omega) := by
    intro omega
    have hpoly : a ^ q + X omega ^ q ≤
        (a ^ q + (q * A) ^ q) * Real.exp (X omega / A) := by
      have heone : 1 ≤ Real.exp (X omega / A) := by
        apply Real.one_le_exp
        exact div_nonneg (hX0 omega) hA.le
      have hfirst : a ^ q ≤ a ^ q * Real.exp (X omega / A) := by
        exact (le_mul_of_one_le_right (Real.rpow_nonneg ha0 q) heone)
      calc
        a ^ q + X omega ^ q ≤ a ^ q + (q * A) ^ q * Real.exp (X omega / A) :=
          add_le_add (le_refl _) (hXq omega)
        _ ≤ a ^ q * Real.exp (X omega / A) +
              (q * A) ^ q * Real.exp (X omega / A) :=
          by simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hfirst ((q * A) ^ q * Real.exp (X omega / A))
        _ = (a ^ q + (q * A) ^ q) * Real.exp (X omega / A) := by ring
    have hsum : S j omega ≤ a + X omega := hSX omega
    have hS0 : 0 ≤ S j omega := hS0 j omega
    have hbase : 0 ≤ a + X omega := add_nonneg ha0 (hX0 omega)
    calc
      (S j omega ^ k * Real.exp (lam * S j omega)) ^ p =
          S j omega ^ q * Real.exp (theta * S j omega) := by
            rw [Real.mul_rpow (Real.rpow_nonneg hS0 k) (Real.exp_pos _).le,
              ← Real.rpow_mul hS0, ← Real.exp_mul]
            congr 2 <;> ring
      _ ≤ (a + X omega) ^ q * Real.exp (theta * (a + X omega)) := by
            exact mul_le_mul
              (Real.rpow_le_rpow hS0 hsum hq)
              (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum htheta))
              (Real.exp_nonneg _)
              (Real.rpow_nonneg hbase q)
      _ ≤ 2 ^ q * (a ^ q + X omega ^ q) *
            Real.exp (theta * (a + X omega)) := by
            exact mul_le_mul_of_nonneg_right
              (aux_rpow_add_le ha0 (hX0 omega) hq) (Real.exp_nonneg _)
      _ ≤ B * Real.exp (c * X omega) := by
            dsimp [B, c]
            calc
              2 ^ q * (a ^ q + X omega ^ q) *
                    Real.exp (theta * (a + X omega)) =
                  2 ^ q * (a ^ q + X omega ^ q) *
                    (Real.exp (theta * a) * Real.exp (theta * X omega)) := by
                      rw [show theta * (a + X omega) = theta * a + theta * X omega by ring,
                        Real.exp_add]
              _ ≤ 2 ^ q * (a ^ q + (q * A) ^ q) * Real.exp (X omega / A) *
                    (Real.exp (theta * a) * Real.exp (theta * X omega)) := by
                      have h2q : 0 ≤ (2 : ℝ) ^ q := Real.rpow_nonneg (by norm_num) q
                      have hE : 0 ≤ Real.exp (theta * a) * Real.exp (theta * X omega) :=
                        mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
                      have htmp := mul_le_mul_of_nonneg_right
                        (mul_le_mul_of_nonneg_left hpoly
                          h2q) hE
                      convert htmp using 1 <;> ring
              _ = 2 ^ q * (a ^ q + (q * A) ^ q) * Real.exp (theta * a) *
                    Real.exp ((theta + A⁻¹) * X omega) := by
                      have hexp : Real.exp (X omega / A) * Real.exp (theta * X omega) =
                          Real.exp ((theta + A⁻¹) * X omega) := by
                        rw [← Real.exp_add]
                        congr 1
                        ring
                      calc
                        2 ^ q * (a ^ q + (q * A) ^ q) * Real.exp (X omega / A) *
                              (Real.exp (theta * a) * Real.exp (theta * X omega)) =
                            2 ^ q * (a ^ q + (q * A) ^ q) *
                              (Real.exp (theta * a) *
                                (Real.exp (X omega / A) * Real.exp (theta * X omega))) := by ring
                        _ = 2 ^ q * (a ^ q + (q * A) ^ q) * Real.exp (theta * a) *
                              Real.exp ((theta + A⁻¹) * X omega) := by rw [hexp]; ring
  have hExp0 := SubdiffusiveProcess.CoarseGrainingVocab.integral_exp_abs_sub_const_le
    (q := c) (b := 0) hA hc hXmeas hbigX
  have hExp : Integrable (fun omega => Real.exp (c * X omega)) P := by
    simpa [abs_of_nonneg (hX0 _)] using hExp0.1
  have hExpBound :
      (∫ omega, Real.exp (c * X omega) ∂P) ≤
        4 * Real.exp (c ^ 2 * A ^ 2 / 2) := by
    simpa [abs_of_nonneg (hX0 _)] using hExp0.2
  let Dscale : ℝ := disorder ^ q * L ^ (q / 2)
  have hDscale : 0 < Dscale := by
    dsimp [Dscale]
    exact mul_pos (Real.rpow_pos_of_pos hdis _) (Real.rpow_pos_of_pos hL _)
  have hLone : 1 ≤ L := by
    dsimp [L]
    linarith [abs_nonneg (Real.log r)]
  have hsqrtL : 1 ≤ Real.sqrt L := Real.one_le_sqrt.mpr hLone
  have hsqrtpow : (Real.sqrt L) ^ q = L ^ (q / 2) := by
    rw [Real.sqrt_eq_rpow L, ← Real.rpow_mul hL.le]
    congr 1
    ring
  have hTpow :
      (disorder * K * Real.sqrt L) ^ q = Dscale * K ^ q := by
    calc
      (disorder * K * Real.sqrt L) ^ q =
          (disorder * K) ^ q * (Real.sqrt L) ^ q := by
            rw [Real.mul_rpow (mul_nonneg hdis.le hK.le) (Real.sqrt_nonneg L)]
      _ = disorder ^ q * K ^ q * (Real.sqrt L) ^ q := by
            rw [Real.mul_rpow hdis.le hK.le]
      _ = disorder ^ q * L ^ (q / 2) * K ^ q := by rw [hsqrtpow]; ring
      _ = Dscale * K ^ q := by dsimp [Dscale]
  have ha_pow : a ^ q ≤ Dscale * K ^ q := by
    exact (Real.rpow_le_rpow ha0 ha_scale hq).trans_eq hTpow
  have hqa_scale : q * A ≤ disorder * Real.sqrt L * (q * Real.sqrt Cc) := by
    have hqCc : 0 ≤ q * Real.sqrt Cc := mul_nonneg hq (Real.sqrt_nonneg _)
    have hinner : q * Real.sqrt Cc ≤ Real.sqrt L * (q * Real.sqrt Cc) :=
      le_mul_of_one_le_left hqCc hsqrtL
    calc
      q * A = disorder * (q * Real.sqrt Cc) := by dsimp [A]; ring
      _ ≤ disorder * (Real.sqrt L * (q * Real.sqrt Cc)) :=
        mul_le_mul_of_nonneg_left hinner hdis.le
      _ = disorder * Real.sqrt L * (q * Real.sqrt Cc) := by ring
  have hqa_pow :
      (q * A) ^ q ≤ Dscale * (q * Real.sqrt Cc) ^ q := by
    have hpow := Real.rpow_le_rpow (mul_nonneg hq hA.le) hqa_scale hq
    have heq :
        (disorder * Real.sqrt L * (q * Real.sqrt Cc)) ^ q =
          Dscale * (q * Real.sqrt Cc) ^ q := by
      rw [Real.mul_rpow (mul_nonneg hdis.le (Real.sqrt_nonneg _))
        (mul_nonneg hq (Real.sqrt_nonneg _))]
      rw [Real.mul_rpow hdis.le (Real.sqrt_nonneg _)]
      rw [hsqrtpow]
    exact hpow.trans_eq heq
  have hsum_scale :
      a ^ q + (q * A) ^ q ≤ Dscale * (K ^ q + (q * Real.sqrt Cc) ^ q) := by
    calc
      a ^ q + (q * A) ^ q ≤ Dscale * K ^ q + Dscale * (q * Real.sqrt Cc) ^ q :=
        add_le_add ha_pow hqa_pow
      _ = Dscale * (K ^ q + (q * Real.sqrt Cc) ^ q) := by ring
  have hBexp :
      B * (∫ omega, Real.exp (c * X omega) ∂P) ≤
        4 * M * Dscale *
          Real.exp (theta * K * disorder * Real.sqrt L + c ^ 2 * A ^ 2 / 2) := by
    have hBcalc : B * (∫ omega, Real.exp (c * X omega) ∂P) ≤
        4 * (2 ^ q * (a ^ q + (q * A) ^ q)) *
          Real.exp (theta * a + c ^ 2 * A ^ 2 / 2) := by
      dsimp [B]
      calc
        2 ^ q * (a ^ q + (q * A) ^ q) * Real.exp (theta * a) *
              (∫ omega, Real.exp (c * X omega) ∂P) ≤
            2 ^ q * (a ^ q + (q * A) ^ q) * Real.exp (theta * a) *
              (4 * Real.exp (c ^ 2 * A ^ 2 / 2)) := by
                exact mul_le_mul_of_nonneg_left hExpBound (by positivity)
        _ = 4 * (2 ^ q * (a ^ q + (q * A) ^ q)) *
              Real.exp (theta * a + c ^ 2 * A ^ 2 / 2) := by
                calc
                  2 ^ q * (a ^ q + (q * A) ^ q) * Real.exp (theta * a) *
                        (4 * Real.exp (c ^ 2 * A ^ 2 / 2)) =
                      4 * (2 ^ q * (a ^ q + (q * A) ^ q)) *
                        (Real.exp (theta * a) * Real.exp (c ^ 2 * A ^ 2 / 2)) := by ring
                  _ = 4 * (2 ^ q * (a ^ q + (q * A) ^ q)) *
                        Real.exp (theta * a + c ^ 2 * A ^ 2 / 2) := by
                          rw [← Real.exp_add]
    calc
      B * (∫ omega, Real.exp (c * X omega) ∂P) ≤
          4 * (2 ^ q * (a ^ q + (q * A) ^ q)) *
            Real.exp (theta * a + c ^ 2 * A ^ 2 / 2) := hBcalc
      _ ≤ 4 * M * Dscale *
            Real.exp (theta * K * disorder * Real.sqrt L + c ^ 2 * A ^ 2 / 2) := by
              dsimp [M]
              have hpolyM :
                  2 ^ q * (a ^ q + (q * A) ^ q) ≤
                    M * Dscale := by
                dsimp [M]
                exact (mul_le_mul_of_nonneg_left hsum_scale
                  (Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) q)).trans_eq (by ring)
              have hexp : Real.exp (theta * a + c ^ 2 * A ^ 2 / 2) ≤
                  Real.exp (theta * K * disorder * Real.sqrt L + c ^ 2 * A ^ 2 / 2) := by
                apply Real.exp_le_exp.mpr
                have htheta_a : theta * a ≤ theta * K * disorder * Real.sqrt L :=
                  (mul_le_mul_of_nonneg_left ha_scale htheta).trans_eq (by ring)
                exact add_le_add htheta_a (le_refl _)
              have hfirst := mul_le_mul_of_nonneg_left hpolyM
                (show 0 ≤ (4 : ℝ) by norm_num)
              have hfirst' :
                  4 * (2 ^ q * (a ^ q + (q * A) ^ q)) ≤ 4 * M * Dscale := by
                exact hfirst.trans_eq (by ring)
              exact mul_le_mul
                hfirst' hexp
                (by positivity) (by positivity)
  let E : ℝ :=
    (K + Real.sqrt Cc + 1) * lam * disorder * Real.sqrt L +
      Cp * lam ^ 2 * disorder ^ 2
  let R : ℝ := Cpk * (disorder ^ k * L ^ (k / 2)) * Real.exp E
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hCpkpow : Cpk ^ p = 4 * M * Real.exp (1 / 2 : ℝ) := by
    dsimp [Cpk]
    have hW : 0 < 4 * M * Real.exp (1 / 2 : ℝ) := by positivity
    rw [← Real.rpow_mul hW.le]
    congr 1
    field_simp [hp.ne']
    simp
  have hScalepow :
      (disorder ^ k * L ^ (k / 2)) ^ p = Dscale := by
    calc
      (disorder ^ k * L ^ (k / 2)) ^ p =
          (disorder ^ k) ^ p * (L ^ (k / 2)) ^ p := by
            rw [Real.mul_rpow (Real.rpow_nonneg hdis.le _) (Real.rpow_nonneg hL.le _)]
      _ = disorder ^ (k * p) * L ^ ((k / 2) * p) := by
            rw [← Real.rpow_mul hdis.le, ← Real.rpow_mul hL.le]
      _ = Dscale := by
            dsimp [Dscale, q]
            congr 1 <;> ring
  have hRpow : R ^ p =
      4 * M * Dscale *
        Real.exp (1 / 2 + p * E) := by
    dsimp [R]
    have hscale0 : 0 ≤ disorder ^ k * L ^ (k / 2) := by positivity
    calc
      (Cpk * (disorder ^ k * L ^ (k / 2)) * Real.exp E) ^ p =
          Cpk ^ p * (disorder ^ k * L ^ (k / 2)) ^ p * (Real.exp E) ^ p := by
            calc
              (Cpk * (disorder ^ k * L ^ (k / 2)) * Real.exp E) ^ p =
                  (Cpk * (disorder ^ k * L ^ (k / 2))) ^ p * (Real.exp E) ^ p := by
                    rw [Real.mul_rpow (mul_nonneg hCpk.le hscale0) (Real.exp_nonneg _)]
              _ = Cpk ^ p * (disorder ^ k * L ^ (k / 2)) ^ p * (Real.exp E) ^ p := by
                    rw [Real.mul_rpow hCpk.le hscale0]
      _ = 4 * M * Dscale * Real.exp (1 / 2 + p * E) := by
            rw [hCpkpow, hScalepow, ← Real.exp_mul]
            calc
              4 * M * Real.exp (1 / 2) * Dscale * Real.exp (E * p) =
                  4 * M * Dscale *
                    (Real.exp (1 / 2) * Real.exp (E * p)) := by ring
              _ = 4 * M * Dscale * Real.exp (1 / 2 + p * E) := by
                    rw [← Real.exp_add]
                    congr 2
                    ring
  have hc_expand : c ^ 2 * A ^ 2 / 2 =
      theta ^ 2 * A ^ 2 / 2 + theta * A + 1 / 2 := by
    dsimp [c]
    field_simp [hA.ne']
    ring
  have hExpCompare :
      theta * K * disorder * Real.sqrt L + c ^ 2 * A ^ 2 / 2 ≤
        1 / 2 + p * E := by
    rw [hc_expand, hAD]
    dsimp [E, theta, Cp, A]
    have hterm1 : 0 ≤ p * lam * disorder * Real.sqrt L := by positivity
    have hterm2 : 0 ≤ p * lam ^ 2 * disorder ^ 2 := by positivity
    have hterm3 : 0 ≤ p * lam * disorder * Real.sqrt Cc * (Real.sqrt L - 1) := by
      have : 0 ≤ Real.sqrt L - 1 := by linarith
      positivity
    nlinarith only [hterm1, hterm2, hterm3]
  have hQle :
      4 * M * Dscale *
          Real.exp (theta * K * disorder * Real.sqrt L + c ^ 2 * A ^ 2 / 2) ≤
        R ^ p := by
    rw [hRpow]
    have hexp := Real.exp_le_exp.mpr hExpCompare
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  have hInt : B * (∫ omega, Real.exp (c * X omega) ∂P) ≤ R ^ p :=
    hBexp.trans hQle
  have hY0 : ∀ omega, 0 ≤ S j omega ^ k * Real.exp (lam * S j omega) := by
    intro omega
    exact mul_nonneg (Real.rpow_nonneg (hS0 j omega) k) (Real.exp_nonneg _)
  have hnorm := aux_eLpNorm_le_of_exp_bound P hp hB hR hY0 hpoint hExp hInt
  dsimp [R, E, Cp, L, r] at hnorm ⊢
  simpa [div_eq_mul_inv, mul_assoc] using hnorm

end Paper
