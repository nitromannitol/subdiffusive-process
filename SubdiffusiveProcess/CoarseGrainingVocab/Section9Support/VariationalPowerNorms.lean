module

public import Mathlib

@[expose] public section

/-! # Hölder and cancellation for the nonlinear Green estimate -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Hölder with the exact remaining mass power, for an arbitrary positive power. -/
theorem variational_power_holder {X : Type*} [MeasurableSpace X] {mu : Measure X}
    {f v : X → ℝ} (hf : AEStronglyMeasurable f mu) (hv : AEStronglyMeasurable v mu)
    {p q t : ℝ} (hp : 1 < p) (hq : 0 < q) (ht : 0 < t)
    (hbalance : 1 / p + t / q ≤ 1) :
    (∫⁻ x, ENNReal.ofReal (|f x| * ‖v x‖ ^ t) ∂mu) ≤
      eLpNorm f (ENNReal.ofReal p) mu * eLpNorm v (ENNReal.ofReal q) mu ^ t *
        mu univ ^ (1 - 1 / p - t / q) := by
  let r : ℝ := p / (p - 1)
  have hp0 : 0 < p := by linarith
  have hr0 : 0 < r := div_pos hp0 (sub_pos.mpr hp)
  have hinv : 1 / p + 1 / r = 1 := by dsimp only [r]; field_simp; ring
  have hrq : r ≤ q / t := by
    apply (le_div_iff₀ ht).mpr
    have h := hbalance
    rw [div_eq_mul_inv t q] at h
    have h' : t / q ≤ 1 / r := by linarith
    have h'' := (div_le_div_iff₀ hq hr0).mp h'
    nlinarith
  have hholder : Real.HolderTriple p r 1 := ⟨by simpa using hinv, hp0, hr0⟩
  let : ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal r) 1 := by
    simpa only [ENNReal.ofReal_one] using hholder.ennrealOfReal
  have hpowmeas : AEStronglyMeasurable (fun x => ‖v x‖ ^ t) mu :=
    (Real.continuous_rpow_const ht.le).comp_aestronglyMeasurable hv.norm
  have hprod : (∫⁻ x, ENNReal.ofReal (|f x| * ‖v x‖ ^ t) ∂mu) =
      eLpNorm (fun x => f x * ‖v x‖ ^ t) 1 mu := by
    change _ = eLpNorm (f * fun x => ‖v x‖ ^ t) 1 mu
    rw [eLpNorm_one_eq_lintegral_enorm (hf.mul hpowmeas)]
    apply lintegral_congr
    intro x
    simp only [Pi.mul_apply, ← ofReal_norm, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (v x)) t)]
  have hcompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (ENNReal.ofReal_le_ofReal hrq) hpowmeas
  have hexp : ENNReal.ofReal (q / t) * ENNReal.ofReal t = ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ q / t), div_mul_cancel₀ _ ht.ne']
  rw [eLpNorm_norm_rpow (p := ENNReal.ofReal (q / t)) v hv ht, hexp, ENNReal.toReal_ofReal hr0.le,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ q / t)] at hcompare
  have hmass : 1 / r - 1 / (q / t) = 1 - 1 / p - t / q := by
    have htq : 1 / (q / t) = t / q := by field_simp
    rw [htq]
    linarith
  rw [hmass] at hcompare
  rw [hprod]
  calc
    _ ≤ eLpNorm f (ENNReal.ofReal p) mu *
        eLpNorm (fun x => ‖v x‖ ^ t) (ENNReal.ofReal r) mu := by
      change eLpNorm (f * fun x => ‖v x‖ ^ t) 1 mu ≤ _
      simpa only [smul_eq_mul] using eLpNorm_smul_le_mul_eLpNorm
        (p := ENNReal.ofReal p) (q := ENNReal.ofReal r) (r := 1) hf hpowmeas
    _ ≤ _ := (mul_le_mul' le_rfl hcompare).trans_eq (by ring)

/-- Cancelling a finite nonzero power keeps the coefficient to its first power. -/
theorem variational_cancel_power {N K : ℝ≥0∞} {s : ℝ}
    (hN : N ≠ ⊤) (hs : 1 ≤ s) (h : N ^ (2 * s) ≤ K * N ^ (2 * s - 1)) : N ≤ K := by
  by_cases hz : N = 0
  · rw [hz]
    exact zero_le
  have hpow0 : N ^ (2 * s - 1) ≠ 0 := by
    intro hzero
    rcases ENNReal.rpow_eq_zero_iff.mp hzero with hzero | htop
    · exact hz hzero.1
    · exact hN htop.1
  have hpowtop : N ^ (2 * s - 1) ≠ ⊤ := by
    have hp : 0 ≤ 2 * s - 1 := by linarith
    exact (ENNReal.rpow_lt_top_of_nonneg hp hN).ne
  apply (ENNReal.mul_le_mul_iff_right hpow0 hpowtop).mp
  have heq : N ^ (2 * s) = N * N ^ (2 * s - 1) := by
    calc
      _ = N ^ (1 + (2 * s - 1)) := by congr 1; ring
      _ = _ := by rw [ENNReal.rpow_add _ _ hz hN, ENNReal.rpow_one]
  rw [heq] at h
  simpa only [mul_comm] using h

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
