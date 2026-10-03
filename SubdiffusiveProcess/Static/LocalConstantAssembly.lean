module

public import SubdiffusiveProcess.Static.LocalEstimateClauses

@[expose] public section

/-! # Combining the three local static suppliers

All probability and deterministic monotonicity steps are checked here. The
principal assembly needs only the three independently supplied moment bounds.
-/

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- Enlarging a positive mass constant preserves both bounds. -/
theorem localMassEstimates_mono {d : ℕ} {b : Vec d → ℝ} {y0 : Vec d} {ρ0 K K' : ℝ}
    (hK : 1 ≤ K) (hKK' : K ≤ K') (h : localMassEstimates b y0 ρ0 K) :
    localMassEstimates b y0 ρ0 K' := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hK'0 : 0 < K' := hK0.trans_le hKK'
  intro x r hr hr1 hsub
  obtain ⟨hl, hu⟩ := h x r hr hr1 hsub
  constructor
  · refine (ENNReal.ofReal_le_ofReal ?_).trans hl
    exact mul_le_mul_of_nonneg_right ((inv_le_inv₀ hK'0 hK0).mpr hKK')
      (Real.rpow_nonneg hr.le _)
  · refine hu.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right hKK' (Real.rpow_nonneg hr.le _)

/-- Enlarging the coercivity constant preserves both native Sobolev clauses. -/
theorem localCoercivityEstimates_mono {d p : ℕ} {A : Vec d → ℝ}
    {c : Fin p → Vec d} {s0 s1 : Fin p → ℝ} {K K' B : ℝ}
    (hKK' : K ≤ K') (h : localCoercivityEstimates A c s0 s1 K B) :
    localCoercivityEstimates A c s0 s1 K' B := by
  intro i n k hk
  obtain ⟨h1, h10⟩ := h i n k hk
  have hfac : ENNReal.ofReal (K * (2 : ℝ) ^ (B * n)) ≤
      ENNReal.ofReal (K' * (2 : ℝ) ^ (B * n)) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hKK' (by positivity))
  constructor
  · intro v
    exact (h1 v).trans (mul_le_mul_left hfac _)
  · intro v
    exact (h10 v).trans (mul_le_mul_left hfac _)

/-- Enlarging the harmonic constant preserves the cutoff witnesses. -/
theorem localHarmonicCutoffEstimates_mono {d p : ℕ} {A : Vec d → ℝ}
    {c : Fin p → Vec d} {s0 s1 : Fin p → ℝ} {K K' B : ℝ}
    (hs : ∀ i, 0 < s0 i ∧ s0 i < s1 i)
    (hKK' : K ≤ K') (h : localHarmonicCutoffEstimates A c s0 s1 K B) :
    localHarmonicCutoffEstimates A c s0 s1 K' B := by
  intro i n k hk
  obtain ⟨chi, h01, h1, hsupport, henergy⟩ := h i n k hk
  refine ⟨chi, h01, h1, hsupport, ?_⟩
  intro x r hr hr1
  refine (henergy x r hr hr1).trans (ENNReal.ofReal_le_ofReal ?_)
  have hgap : 0 < (s1 i - s0 i) / 2 ^ n / 2 := by
    exact div_pos (div_pos (sub_pos.mpr (hs i).2) (pow_pos (by norm_num) _)) (by norm_num)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hKK' (Real.rpow_nonneg hgap.le _)) (Real.rpow_nonneg hr.le _)

private theorem ofReal_max_rpow_le (a b q : ℝ) :
    ENNReal.ofReal ((max a b) ^ q) ≤ ENNReal.ofReal (a ^ q) + ENNReal.ofReal (b ^ q) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]
    exact le_add_of_nonneg_left zero_le
  · rw [max_eq_left h]
    exact le_add_of_nonneg_right zero_le

/-- A maximum pays only the sum of the original moments. -/
theorem moment_max_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {K1 K2 : Ω → ℝ} (hK1 : Measurable K1) (hK2 : Measurable K2) (q : ℝ)
    {C1 C2 : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (h1 : (∫⁻ ω, ENNReal.ofReal (K1 ω ^ q) ∂μ) ≤ ENNReal.ofReal C1)
    (h2 : (∫⁻ ω, ENNReal.ofReal (K2 ω ^ q) ∂μ) ≤ ENNReal.ofReal C2) :
    (∫⁻ ω, ENNReal.ofReal ((max (K1 ω) (K2 ω)) ^ q) ∂μ) ≤ ENNReal.ofReal (C1 + C2) := by
  refine (lintegral_mono fun ω => ofReal_max_rpow_le (K1 ω) (K2 ω) q).trans ?_
  have hpow : Measurable (fun ω => ENNReal.ofReal (K2 ω ^ q)) :=
    ENNReal.measurable_ofReal.comp (hK2.pow_const q)
  rw [lintegral_add_right _ hpow]
  exact (add_le_add h1 h2).trans_eq (ENNReal.ofReal_add hC1 hC2).symm

/-- The mass, coercivity and harmonic suppliers have one common measurable
constant and the exact conjunction needed by the principal theorem. -/
theorem exists_common_static_constant {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {d p : ℕ} (b A : Ω → Vec d → ℝ) (y0 : Vec d) (ρ0 : ℝ)
    (c : Fin p → Vec d) (s0 s1 : Fin p → ℝ) (hs : ∀ i, 0 < s0 i ∧ s0 i < s1 i)
    (q B : ℝ) {Cmass Ccoer Ccut : ℝ}
    (hCmass : 0 ≤ Cmass) (hCcoer : 0 ≤ Ccoer) (hCcut : 0 ≤ Ccut)
    (hmass : ∃ K : Ω → ℝ, Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
      (∫⁻ ω, ENNReal.ofReal (K ω ^ q) ∂μ) ≤ ENNReal.ofReal Cmass ∧
        ∀ᵐ ω ∂μ, localMassEstimates (b ω) y0 ρ0 (K ω))
    (hcoer : ∃ K : Ω → ℝ, Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
      (∫⁻ ω, ENNReal.ofReal (K ω ^ q) ∂μ) ≤ ENNReal.ofReal Ccoer ∧
        ∀ᵐ ω ∂μ, localCoercivityEstimates (A ω) c s0 s1 (K ω) B)
    (hcut : ∃ K : Ω → ℝ, Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
      (∫⁻ ω, ENNReal.ofReal (K ω ^ q) ∂μ) ≤ ENNReal.ofReal Ccut ∧
        ∀ᵐ ω ∂μ, localHarmonicCutoffEstimates (A ω) c s0 s1 (K ω) B) :
    ∃ K : Ω → ℝ, Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
      (∫⁻ ω, ENNReal.ofReal (K ω ^ q) ∂μ) ≤ ENNReal.ofReal (Cmass + (Ccoer + Ccut)) ∧
        ∀ᵐ ω ∂μ, SubdiffusiveProcess.Static.estimates (b ω) (A ω) y0 ρ0 c s0 s1 (K ω) B := by
  obtain ⟨Km, hKm, hKm1, hKmmom, hKmass⟩ := hmass
  obtain ⟨Kc, hKc, hKc1, hKcmom, hKcoer⟩ := hcoer
  obtain ⟨Kh, hKh, hKh1, hKhmom, hKcut⟩ := hcut
  let K : Ω → ℝ := fun ω => max (Km ω) (max (Kc ω) (Kh ω))
  have hKmeas : Measurable K := hKm.max (hKc.max hKh)
  have hmK : ∀ ω, Km ω ≤ K ω := fun ω => le_max_left _ _
  have hcK : ∀ ω, Kc ω ≤ K ω := fun ω => (le_max_left _ _).trans (le_max_right _ _)
  have hhK : ∀ ω, Kh ω ≤ K ω := fun ω => (le_max_right _ _).trans (le_max_right _ _)
  have hKone : ∀ ω, 1 ≤ K ω := fun ω => (hKm1 ω).trans (hmK ω)
  have hmoment := moment_max_le μ hKm (hKc.max hKh) q hCmass (add_nonneg hCcoer hCcut)
    hKmmom (moment_max_le μ hKc hKh q hCcoer hCcut hKcmom hKhmom)
  refine ⟨K, hKmeas, hKone, hmoment, ?_⟩
  filter_upwards [hKmass, hKcoer, hKcut] with ω hm hc hh
  exact (estimates_iff_clauses _ _ _ _ _ _ _ _ _).mpr
    ⟨localMassEstimates_mono (hKm1 ω) (hmK ω) hm,
      localCoercivityEstimates_mono (hcK ω) hc,
      localHarmonicCutoffEstimates_mono hs (hhK ω) hh⟩

end SubdiffusiveProcess.Static
