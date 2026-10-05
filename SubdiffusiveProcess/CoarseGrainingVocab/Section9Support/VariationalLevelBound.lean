module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.VariationalLevelIteration

@[expose] public section

/-!
# The variational endpoint from positive-level estimates

The level iteration starts from the total mass, so it needs no assumed
high-integrability or contraction estimate for the unknown solution.
All constants depend only on the supplied Sobolev exponent.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Homogenization Filter Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal NNReal Topology

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Positive-level Sobolev control yields the critical forcing-to-infinity
gain, starting with only `L²` integrability of the solution. -/
theorem variational_ae_le_of_level_estimates {α : Type*} [MeasurableSpace α]
    (mu : Measure α) [IsFiniteMeasure mu] {p B : ℝ} (hp : 2 < p) (hB : 0 < B)
    (hM : 0 < (mu univ).toReal) {u f : α → ℝ}
    (hu : MemLp u 2 mu) (hf : MemLp f (ENNReal.ofReal (2 / (1 - 2 / p))) mu)
    (hLevel : ∀ k : ℝ, 0 ≤ k →
      (eLpNorm (fun x => max (u x - k) 0) (ENNReal.ofReal p) mu) ^ 2 ≤
        ENNReal.ofReal B * ∫⁻ x, ENNReal.ofReal (|f x| * max (u x - k) 0) ∂mu) :
    ∀ᵐ x ∂mu, u x ≤ stampacchiaConstant p * B *
      (mu univ).toReal ^ (1 / (2 / (1 - 2 / p))) *
        (eLpNorm f (ENNReal.ofReal (2 / (1 - 2 / p))) mu).toReal := by
  let q : ℝ := 2 / (1 - 2 / p)
  let aExp : ℝ := p / 2
  let bExp : ℝ := aExp - 1
  let C : ℝ := ((4 : ℝ) ^ aExp) ^ (1 / (2 * bExp))
  let N : ℝ := (eLpNorm f (ENNReal.ofReal q) mu).toReal
  obtain ⟨_, hq2, hbalance, hqb⟩ := stampacchia_exponents hp
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by dsimp only [q]; linarith
  have haExp : 0 < aExp := by dsimp only [aExp]; positivity
  have haExp1 : 1 < aExp := by dsimp only [aExp]; linarith
  have hbExp : 0 < bExp := by dsimp only [bExp]; linarith
  have hC : 0 < C := by dsimp only [C]; positivity
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  by_cases hNz : N = 0
  · have hfn : eLpNorm f (ENNReal.ofReal q) mu = 0 :=
      ((ENNReal.toReal_eq_zero_iff _).mp hNz).resolve_right hf.eLpNorm_ne_top
    have hfzero := (eLpNorm_eq_zero_iff
      (ne_of_gt (ENNReal.ofReal_pos.mpr hq0))).mp hfn
    have hzero : (∫⁻ x, ENNReal.ofReal (|f x| * max (u x - 0) 0) ∂mu) = 0 := by
      calc
        _ = ∫⁻ _x, (0 : ℝ≥0∞) ∂mu := by
          apply lintegral_congr_ae
          filter_upwards [hfzero] with x hx
          simp only [Pi.zero_apply] at hx
          simp only [hx, abs_zero, zero_mul, ENNReal.ofReal_zero]
        _ = 0 := lintegral_zero
    have hnormsq := hLevel 0 le_rfl
    rw [hzero, mul_zero] at hnormsq
    have hnorm : eLpNorm (fun x => max (u x - 0) 0) (ENNReal.ofReal p) mu = 0 :=
      eq_zero_of_pow_eq_zero (le_antisymm hnormsq (zero_le))
    have hueq := (eLpNorm_eq_zero_iff
      (ne_of_gt (ENNReal.ofReal_pos.mpr hp0))).mp hnorm
    filter_upwards [hueq] with x hx
    have hux : u x ≤ 0 := by
      have hle := le_max_left (u x) 0
      simpa only [sub_zero, Pi.zero_apply] using hle.trans (by simpa only [sub_zero, Pi.zero_apply] using hx.le)
    change u x ≤ stampacchiaConstant p * B * (mu univ).toReal ^ (1 / q) * N
    simpa only [hNz, mul_zero] using hux
  have hN : 0 < N := lt_of_le_of_ne hN0 (Ne.symm hNz)
  let L : ℝ := (mu univ).toReal ^ (1 / q)
  let E0 : ℝ := B * N
  let K : ℝ := C * L * E0
  let a : ℝ → ℝ := fun k => (mu {x | k < u x}).toReal
  have hL : 0 < L := Real.rpow_pos_of_pos hM _
  have hE0 : 0 < E0 := mul_pos hB hN
  have hK : 0 < K := mul_pos (mul_pos hC hL) hE0
  have hLd : 0 < L ^ q := Real.rpow_pos_of_pos hL _
  have hLpow : L ^ q = (mu univ).toReal := by
    simpa only [L, one_div] using Real.rpow_inv_rpow hM.le hq0.ne'
  have hinit : a (deGiorgiLevel K 0) ≤ L ^ q := by
    rw [hLpow, deGiorgiLevel_zero]
    exact ENNReal.toReal_mono (measure_ne_top mu univ) (measure_mono (subset_univ _))
  have hrec : ∀ k l : ℝ, 0 ≤ k → k < l →
      (l - k) ^ 2 * (a l) ^ (2 / p) ≤ (B ^ 2 * N ^ 2) * a k := by
    intro k l hk hkl
    exact variational_level_volume_recursion mu hp0 hq2.le hbalance hB.le hu hf hLevel hk hkl
  have hcritical : q * bExp = 2 * aExp := by
    change q * (p / 2 - 1) = 2 * (p / 2)
    nlinarith [hqb]
  have hadm := deGiorgi_admissible_real_exponent (d := q) (C_F := 1) (E₀ := E0)
    (L := L) (Cd := C) (α := aExp) (β := bExp) haExp hbExp rfl hcritical
    (by norm_num) hE0 hL hC (by simp only [one_mul]; exact le_rfl)
  have hKcond : ((B ^ 2 * N ^ 2) / K ^ 2) ^ aExp * (4 : ℝ) ^ aExp * (L ^ q) ^ bExp ≤
      ((4 : ℝ) ^ aExp) ^ (-(1 / bExp)) := by
    simpa only [E0, K, one_pow, one_mul, mul_pow] using hadm
  have hdecay := deGiorgi_levelVolume_tendsto_zero (a := a) (Ld := L ^ q)
    (Crec := B ^ 2 * N ^ 2) (K := K) (α := aExp) (β := bExp) (γ := 2 / p) (B := (4 : ℝ) ^ aExp)
    (fun _ => ENNReal.toReal_nonneg) hLd (by positivity) hK haExp1 rfl
    (by dsimp only [aExp]; field_simp) rfl hinit hrec hKcond
  have hAE := ae_le_of_deGiorgi_level_decay (m := 0) mu u hK (by simpa only [zero_add] using hdecay)
  have hCbound : C ≤ stampacchiaConstant p := by
    change C ≤ 1 + C
    linarith
  filter_upwards [hAE] with x hx
  apply (show u x ≤ K by simpa only [zero_add] using hx).trans
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCbound hB.le) hL.le) hN.le
  convert h using 1
  dsimp only [K, E0]
  ring

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
