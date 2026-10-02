import SubdiffusiveProcess.Static.Estimates
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! # Stability of the local static estimates under a scalar comparison

A single two-sided bound on each density and energy coefficient transports
all three estimates. The cutoff witnesses are retained. This permits finite
infrared factors to be compared with the characterized full infrared field.
-/

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- The unnormalized fractional Sobolev squared norm used in the static estimate. -/
def fractionalSqNorm {d : ℕ} (U : Set (Vec d)) (v : Vec d → ℝ) : ℝ≥0∞ :=
  (∫⁻ x in U, ∫⁻ z in U, ENNReal.ofReal ((v x - v z) ^ 2) /
    ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))) +
    ∫⁻ x in U, ENNReal.ofReal (v x ^ 2)

/-- The energy integral on a set, including its boundary-independent local version. -/
def energy {d : ℕ} (U : Set (Vec d)) (A : Vec d → ℝ) (Dv : Vec d → Vec d) : ℝ≥0∞ :=
  ∫⁻ x in U, ENNReal.ofReal (A x * Homogenization.vecDot (Dv x) (Dv x))

/-- Scalar comparison of nonnegative lower integrals on a measurable set. -/
theorem lintegral_ofReal_le_mul {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {U : Set X} (hU : MeasurableSet U) {f g : X → ℝ} {F : ℝ} (hF : 0 ≤ F)
    (hfg : ∀ x ∈ U, f x ≤ F * g x) :
    (∫⁻ x in U, ENNReal.ofReal (f x) ∂μ) ≤
      ENNReal.ofReal F * ∫⁻ x in U, ENNReal.ofReal (g x) ∂μ := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hU] with x hx
  rw [← ENNReal.ofReal_mul hF]
  exact ENNReal.ofReal_le_ofReal (hfg x hx)

/-- Scalar comparison of energy, requiring no integrability premise. -/
theorem energy_le_mul {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U)
    {A0 A1 : Vec d → ℝ} {F : ℝ} (hF : 0 ≤ F)
    (hA : ∀ x ∈ U, A0 x ≤ F * A1 x) (Dv : Vec d → Vec d) :
    energy U A0 Dv ≤ ENNReal.ofReal F * energy U A1 Dv := by
  apply lintegral_ofReal_le_mul volume hU hF
  intro x hx
  have hnn := Homogenization.vecNormSq_nonneg (Dv x)
  change 0 ≤ Homogenization.vecDot (Dv x) (Dv x) at hnn
  calc
    A0 x * Homogenization.vecDot (Dv x) (Dv x) ≤
        (F * A1 x) * Homogenization.vecDot (Dv x) (Dv x) :=
      mul_le_mul_of_nonneg_right (hA x hx) hnn
    _ = F * (A1 x * Homogenization.vecDot (Dv x) (Dv x)) := mul_assoc _ _ _

/-- The local mass of a density, as a nonnegative lower integral. -/
theorem density_mass_eq_lintegral {d : ℕ} (b : Vec d → ℝ) {U : Set (Vec d)}
    (hU : MeasurableSet U) :
    volume.withDensity (fun x => ENNReal.ofReal (b x)) U =
      ∫⁻ x in U, ENNReal.ofReal (b x) :=
  withDensity_apply _ hU

/-- Transport of all three static estimates using a common scalar factor. -/
theorem estimates_of_comparison {d p : ℕ} {b0 b1 A0 A1 : Vec d → ℝ}
    {y0 : Vec d} {ρ0 K B F : ℝ} {c : Fin p → Vec d} {s0 s1 : Fin p → ℝ}
    (hK : 1 ≤ K) (hF : 1 ≤ F)
    (hs : ∀ i, 0 < s0 i ∧ s0 i < s1 i)
    (hin : ∀ i, Metric.ball (c i) (s1 i / 2) ⊆ Metric.ball y0 (ρ0 / 2))
    (hbLow : ∀ x ∈ Metric.ball y0 (ρ0 / 2), F⁻¹ * b0 x ≤ b1 x)
    (hbUp : ∀ x ∈ Metric.ball y0 (ρ0 / 2), b1 x ≤ F * b0 x)
    (hALow : ∀ x ∈ Metric.ball y0 (ρ0 / 2), A0 x ≤ F * A1 x)
    (hAUp : ∀ x ∈ Metric.ball y0 (ρ0 / 2), A1 x ≤ F * A0 x)
    (h : estimates b0 A0 y0 ρ0 c s0 s1 K B) :
    estimates b1 A1 y0 ρ0 c s0 s1 (F * K) B := by
  have hF0 : 0 ≤ F := zero_le_one.trans hF
  have hFinv : 0 ≤ F⁻¹ := inv_nonneg.mpr hF0
  have hFenn : 1 ≤ ENNReal.ofReal F := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hF
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hnest : ∀ i : Fin p, ∀ n k : ℕ, k ≤ 2 ^ n →
      Metric.ball (c i)
        (((1 - (k : ℝ) / 2 ^ n) * s0 i + ((k : ℝ) / 2 ^ n) * s1 i) / 2) ⊆
          Metric.ball y0 (ρ0 / 2) := by
    intro i n k hk
    apply Set.Subset.trans (Metric.ball_subset_ball ?_) (hin i)
    have hn : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) _
    have hk' : (k : ℝ) ≤ 2 ^ n := by exact_mod_cast hk
    have hz : 0 ≤ (k : ℝ) / 2 ^ n := div_nonneg (Nat.cast_nonneg _) hn.le
    have ho : (k : ℝ) / 2 ^ n ≤ 1 := (div_le_one hn).mpr hk'
    have hprod := mul_nonneg (sub_nonneg.mpr ho) (sub_nonneg.mpr (hs i).2.le)
    nlinarith only [hprod]
  refine ⟨?_, ?_, ?_⟩
  · intro x r hr hr1 hsub
    obtain ⟨hlo, hup⟩ := h.1 x r hr hr1 hsub
    have hball : MeasurableSet (Metric.ball x r) := Metric.isOpen_ball.measurableSet
    have hml : ENNReal.ofReal F⁻¹ *
        volume.withDensity (fun z => ENNReal.ofReal (b0 z)) (Metric.ball x r) ≤
          volume.withDensity (fun z => ENNReal.ofReal (b1 z)) (Metric.ball x r) := by
      rw [density_mass_eq_lintegral _ hball, density_mass_eq_lintegral _ hball]
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hball] with z hz
      rw [← ENNReal.ofReal_mul hFinv]
      exact ENNReal.ofReal_le_ofReal (hbLow z (hsub hz))
    have hmu : volume.withDensity (fun z => ENNReal.ofReal (b1 z)) (Metric.ball x r) ≤
        ENNReal.ofReal F *
          volume.withDensity (fun z => ENNReal.ofReal (b0 z)) (Metric.ball x r) := by
      rw [density_mass_eq_lintegral _ hball, density_mass_eq_lintegral _ hball]
      exact lintegral_ofReal_le_mul volume hball hF0 (fun z hz => hbUp z (hsub hz))
    constructor
    · calc
        ENNReal.ofReal ((F * K)⁻¹ * r ^ ((d : ℝ) + 1 / 2)) =
            ENNReal.ofReal F⁻¹ * ENNReal.ofReal (K⁻¹ * r ^ ((d : ℝ) + 1 / 2)) := by
          rw [← ENNReal.ofReal_mul hFinv, mul_inv, mul_assoc]
        _ ≤ ENNReal.ofReal F⁻¹ *
            volume.withDensity (fun z => ENNReal.ofReal (b0 z)) (Metric.ball x r) :=
          mul_le_mul_right hlo _
        _ ≤ _ := hml
    · calc
        _ ≤ ENNReal.ofReal F *
            volume.withDensity (fun z => ENNReal.ofReal (b0 z)) (Metric.ball x r) := hmu
        _ ≤ ENNReal.ofReal F * ENNReal.ofReal (K * r ^ ((d : ℝ) - 1 / 2)) :=
          mul_le_mul_right hup _
        _ = _ := by rw [← ENNReal.ofReal_mul hF0, mul_assoc]
  · intro i n k hk
    let U := Metric.ball (c i)
      (((1 - (k : ℝ) / 2 ^ n) * s0 i + ((k : ℝ) / 2 ^ n) * s1 i) / 2)
    have hU : MeasurableSet U := Metric.isOpen_ball.measurableSet
    have hUsub : U ⊆ Metric.ball y0 (ρ0 / 2) := hnest i n k hk
    have hfac : ENNReal.ofReal (K * (2 : ℝ) ^ (B * n)) * ENNReal.ofReal F =
        ENNReal.ofReal ((F * K) * (2 : ℝ) ^ (B * n)) := by
      rw [mul_comm, ← ENNReal.ofReal_mul hF0, ← mul_assoc]
    obtain ⟨hh1, hh10⟩ := h.2.1 i n k hk
    constructor
    · intro v
      change fractionalSqNorm U v.toFun ≤
        ENNReal.ofReal ((F * K) * (2 : ℝ) ^ (B * n)) *
          (energy U A1 v.grad + ∫⁻ x in U, ENNReal.ofReal (v.toFun x ^ 2))
      have hE := energy_le_mul hU hF0 (fun x hx => hALow x (hUsub hx)) v.grad
      have hL : (∫⁻ x in U, ENNReal.ofReal (v.toFun x ^ 2)) ≤
          ENNReal.ofReal F * ∫⁻ x in U, ENNReal.ofReal (v.toFun x ^ 2) := by
        simpa only [one_mul] using mul_le_mul_left hFenn
          (∫⁻ x in U, ENNReal.ofReal (v.toFun x ^ 2))
      calc
        _ ≤ ENNReal.ofReal (K * (2 : ℝ) ^ (B * n)) *
            (energy U A0 v.grad + ∫⁻ x in U, ENNReal.ofReal (v.toFun x ^ 2)) := hh1 v
        _ ≤ ENNReal.ofReal (K * (2 : ℝ) ^ (B * n)) *
            (ENNReal.ofReal F *
              (energy U A1 v.grad + ∫⁻ x in U, ENNReal.ofReal (v.toFun x ^ 2))) := by
          apply mul_le_mul_right _ _
          simpa only [mul_add] using add_le_add hE hL
        _ = _ := by rw [← mul_assoc, hfac]
    · intro v
      change fractionalSqNorm U v.toFun ≤
        ENNReal.ofReal ((F * K) * (2 : ℝ) ^ (B * n)) * energy U A1 v.grad
      calc
        _ ≤ ENNReal.ofReal (K * (2 : ℝ) ^ (B * n)) * energy U A0 v.grad := hh10 v
        _ ≤ ENNReal.ofReal (K * (2 : ℝ) ^ (B * n)) *
            (ENNReal.ofReal F * energy U A1 v.grad) :=
          mul_le_mul_right (energy_le_mul hU hF0 (fun x hx => hALow x (hUsub hx)) v.grad) _
        _ = _ := by rw [← mul_assoc, hfac]
  · intro i n k hk
    obtain ⟨chi, hchi0, hchi1, hsupport, henergy⟩ := h.2.2 i n k hk
    refine ⟨chi, hchi0, hchi1, hsupport, ?_⟩
    intro x r hr hr1
    let U := Metric.ball x r ∩ Metric.ball (c i)
      (((1 - ((k + 1 : ℕ) : ℝ) / 2 ^ n) * s0 i +
        (((k + 1 : ℕ) : ℝ) / 2 ^ n) * s1 i) / 2)
    have hU : MeasurableSet U := Metric.isOpen_ball.measurableSet.inter
      Metric.isOpen_ball.measurableSet
    have hE := energy_le_mul hU hF0 (fun z hz =>
      hAUp z (hnest i n (k + 1) (by omega) hz.2)) chi.grad
    calc
      _ ≤ ENNReal.ofReal F * energy U A0 chi.grad := hE
      _ ≤ ENNReal.ofReal F *
          ENNReal.ofReal (K * ((s1 i - s0 i) / 2 ^ n / 2) ^ (-B) *
            r ^ ((d : ℝ) - 1 / 2)) := mul_le_mul_right (henergy x r hr hr1) _
      _ = _ := by rw [← ENNReal.ofReal_mul hF0]; congr 1; ring

/-- Enlarging the common constant preserves every estimate and cutoff witness. -/
theorem estimates_mono_constant {d p : ℕ} {b A : Vec d → ℝ}
    {y0 : Vec d} {ρ0 K K' B : ℝ} {c : Fin p → Vec d} {s0 s1 : Fin p → ℝ}
    (hK : 1 ≤ K) (hKK' : K ≤ K')
    (hs : ∀ i, 0 < s0 i ∧ s0 i < s1 i)
    (h : estimates b A y0 ρ0 c s0 s1 K B) :
    estimates b A y0 ρ0 c s0 s1 K' B := by
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK
  have hK'pos : 0 < K' := hKpos.trans_le hKK'
  refine ⟨?_, ?_, ?_⟩
  · intro x r hr hr1 hsub
    obtain ⟨hl, hu⟩ := h.1 x r hr hr1 hsub
    constructor
    · apply le_trans (ENNReal.ofReal_le_ofReal ?_) hl
      exact mul_le_mul_of_nonneg_right ((inv_le_inv₀ hK'pos hKpos).mpr hKK')
        (Real.rpow_nonneg hr.le _)
    · apply le_trans hu (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right hKK' (Real.rpow_nonneg hr.le _)
  · intro i n k hk
    obtain ⟨h1, h10⟩ := h.2.1 i n k hk
    have hfac : ENNReal.ofReal (K * (2 : ℝ) ^ (B * n)) ≤
        ENNReal.ofReal (K' * (2 : ℝ) ^ (B * n)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hKK' (by positivity))
    constructor
    · intro v
      exact (h1 v).trans (mul_le_mul_left hfac _)
    · intro v
      exact (h10 v).trans (mul_le_mul_left hfac _)
  · intro i n k hk
    obtain ⟨chi, h01, h1, hsupp, he⟩ := h.2.2 i n k hk
    refine ⟨chi, h01, h1, hsupp, ?_⟩
    intro x r hr hr1
    apply (he x r hr hr1).trans (ENNReal.ofReal_le_ofReal ?_)
    have hgap : 0 < (s1 i - s0 i) / 2 ^ n / 2 := by
      exact div_pos (div_pos (sub_pos.mpr (hs i).2) (pow_pos (by norm_num) _))
        (by norm_num)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKK' (Real.rpow_nonneg hgap.le _))
      (Real.rpow_nonneg hr.le _)

end SubdiffusiveProcess.Static
