import SubdiffusiveProcess.Probability.Diffusion.Packet452DoobL2
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic




open MeasureTheory Filter Set

open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess

/-- **Doob's `L^p` maximal inequality**, abstract form, constant `2 ^ p * p / (p - 1)`.
If a nonnegative measurable `S` satisfies the WEAK maximal inequality
`t * mu {S ≥ t} ≤ ∫_{S ≥ t} g` at every positive level against a nonnegative
measurable `g`, then `∫ S ^ p ≤ 2 ^ p * p/(p-1) * ∫ g ^ p`. -/
theorem doob_lp_maximal
    {Omega : Type*} {m0 : MeasurableSpace Omega} {mu : Measure Omega}
    [IsFiniteMeasure mu] (S g : Omega → ℝ) (p : ℕ) (hp : 2 ≤ p)
    (hSmble : Measurable S) (hSnn : ∀ omega, 0 ≤ S omega)
    (hgmble : Measurable g) (hgnn : ∀ omega, 0 ≤ g omega)
    (hweak : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * mu {omega | t ≤ S omega} ≤
      ∫⁻ omega in {omega | t ≤ S omega}, ENNReal.ofReal (g omega) ∂mu) :
    ∫⁻ omega, ENNReal.ofReal (S omega ^ p) ∂mu ≤
      ENNReal.ofReal ((2 : ℝ) ^ p * ((p : ℝ) / ((p : ℝ) - 1))) *
        ∫⁻ omega, ENNReal.ofReal (g omega ^ p) ∂mu := by
  classical
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp1 : (1 : ℝ) < (p : ℝ) := by linarith
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  set qr : ℝ := (p : ℝ) / ((p : ℝ) - 1) with hqrdef
  have hqr0 : 0 < qr := div_pos hp0 hpm1
  have hgenn : Measurable fun omega => ENNReal.ofReal (g omega) := hgmble.ennreal_ofReal
  set nu : Measure Omega := mu.withDensity (fun omega => ENNReal.ofReal (g omega)) with hnudef
  have hsetS : ∀ t : ℝ, MeasurableSet {omega | t ≤ S omega} :=
    fun t => measurableSet_le measurable_const hSmble
  have hset2 : ∀ t : ℝ, MeasurableSet {omega | t ≤ 2 * g omega} :=
    fun t => measurableSet_le measurable_const (measurable_const.mul hgmble)
  -- Step 1: the splitting of the weak inequality.
  have hsplit : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t * mu {omega | t ≤ S omega} ≤
        2 * nu {omega | t ≤ 2 * g omega} := by
    intro t ht
    have hbound : ∀ omega, ENNReal.ofReal (g omega) ≤
        Set.indicator {omega | t ≤ 2 * g omega}
          (fun omega => ENNReal.ofReal (g omega)) omega + ENNReal.ofReal (t / 2) := by
      intro omega
      by_cases hc : t ≤ 2 * g omega
      · have : omega ∈ {omega | t ≤ 2 * g omega} := hc
        rw [Set.indicator_of_mem this]
        exact le_add_right le_rfl
      · have hnot : omega ∉ {omega | t ≤ 2 * g omega} := hc
        rw [Set.indicator_of_notMem hnot, zero_add]
        push_neg at hc
        exact ENNReal.ofReal_le_ofReal (by linarith)
    have hstep1 : ∫⁻ omega in {omega | t ≤ S omega}, ENNReal.ofReal (g omega) ∂mu
        ≤ nu {omega | t ≤ 2 * g omega}
          + ENNReal.ofReal (t / 2) * mu {omega | t ≤ S omega} := by
      calc ∫⁻ omega in {omega | t ≤ S omega}, ENNReal.ofReal (g omega) ∂mu
          ≤ ∫⁻ omega in {omega | t ≤ S omega},
              (Set.indicator {omega | t ≤ 2 * g omega}
                (fun omega => ENNReal.ofReal (g omega)) omega
                  + ENNReal.ofReal (t / 2)) ∂mu := lintegral_mono hbound
        _ = (∫⁻ omega in {omega | t ≤ S omega},
              Set.indicator {omega | t ≤ 2 * g omega}
                (fun omega => ENNReal.ofReal (g omega)) omega ∂mu)
            + ENNReal.ofReal (t / 2) * mu {omega | t ≤ S omega} := by
              rw [lintegral_add_right _ measurable_const, setLIntegral_const]
        _ ≤ nu {omega | t ≤ 2 * g omega}
            + ENNReal.ofReal (t / 2) * mu {omega | t ≤ S omega} := by
              have hind : (∫⁻ omega in {omega | t ≤ S omega},
                  Set.indicator {omega | t ≤ 2 * g omega}
                    (fun omega => ENNReal.ofReal (g omega)) omega ∂mu)
                  ≤ nu {omega | t ≤ 2 * g omega} := by
                rw [hnudef, withDensity_apply _ (hset2 t),
                  ← lintegral_indicator (hset2 t)]
                exact setLIntegral_le_lintegral _ _
              exact add_le_add hind le_rfl
    set b : ℝ≥0∞ := ENNReal.ofReal (t / 2) * mu {omega | t ≤ S omega} with hbdef
    have ha2b : ENNReal.ofReal t * mu {omega | t ≤ S omega} = 2 * b := by
      rw [hbdef, ← mul_assoc]
      congr 1
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    have hbfin : b ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top mu _)
    have hkey : b ≤ nu {omega | t ≤ 2 * g omega} := by
      have hle : b + b ≤ nu {omega | t ≤ 2 * g omega} + b := by
        rw [← two_mul, ← ha2b]
        exact le_trans (hweak t ht) hstep1
      exact (ENNReal.add_le_add_iff_right hbfin).mp hle
    calc ENNReal.ofReal t * mu {omega | t ≤ S omega} = 2 * b := ha2b
      _ ≤ 2 * nu {omega | t ≤ 2 * g omega} := mul_le_mul_right hkey 2
  -- Step 2: the first layer cake, for S under mu.
  have hprim1 : ∀ x : ℝ, ∫ t in (0 : ℝ)..x, (p : ℝ) * t ^ (p - 1) = x ^ p := by
    intro x
    have h1 : (1 : ℕ) ≤ p := by omega
    have hsucc : p - 1 + 1 = p := by omega
    have hcast : ((p - 1 : ℕ) : ℝ) + 1 = (p : ℝ) := by
      rw [Nat.cast_sub h1]; push_cast; ring
    rw [intervalIntegral.integral_const_mul, integral_pow, hcast, hsucc,
      zero_pow (by omega : p ≠ 0), sub_zero]
    field_simp
  have hlayer1 : ∫⁻ omega, ENNReal.ofReal (S omega ^ p) ∂mu
      = ∫⁻ t in Set.Ioi (0 : ℝ), mu {omega | t ≤ S omega} *
          ENNReal.ofReal ((p : ℝ) * t ^ (p - 1)) := by
    have h := MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul (μ := mu) (f := S)
      (g := fun t => (p : ℝ) * t ^ (p - 1)) (Eventually.of_forall hSnn)
      hSmble.aemeasurable
      (fun t _ => (continuous_const.mul (continuous_pow _)).intervalIntegrable 0 t)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall (fun t ht => by
        have htpos : (0 : ℝ) < t := ht
        positivity)))
    simpa only [hprim1] using h
  -- Step 3: the second layer cake, for 2 g under nu.
  have hprim2 : ∀ x : ℝ, ∫ t in (0 : ℝ)..x, (p : ℝ) * t ^ (p - 2)
      = qr * x ^ (p - 1) := by
    intro x
    have h2 : (2 : ℕ) ≤ p := hp
    have hsucc : p - 2 + 1 = p - 1 := by omega
    have hcast : ((p - 2 : ℕ) : ℝ) + 1 = (p : ℝ) - 1 := by
      rw [Nat.cast_sub h2]; push_cast; ring
    rw [intervalIntegral.integral_const_mul, integral_pow, hcast, hsucc,
      zero_pow (by omega : p - 1 ≠ 0), sub_zero, hqrdef]
    field_simp
  have hlayer2 : ∫⁻ t in Set.Ioi (0 : ℝ), nu {omega | t ≤ 2 * g omega} *
        ENNReal.ofReal ((p : ℝ) * t ^ (p - 2))
      = ∫⁻ omega, ENNReal.ofReal (qr * (2 * g omega) ^ (p - 1)) ∂nu := by
    have h := MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul (μ := nu)
      (f := fun omega => 2 * g omega) (g := fun t => (p : ℝ) * t ^ (p - 2))
      (Eventually.of_forall (fun omega => by
        have h := hgnn omega
        show (0 : ℝ) ≤ 2 * g omega
        linarith))
      (measurable_const.mul hgmble).aemeasurable
      (fun t _ => (continuous_const.mul (continuous_pow _)).intervalIntegrable 0 t)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall (fun t ht => by
        have htpos : (0 : ℝ) < t := ht
        positivity)))
    simpa only [hprim2] using h.symm
  -- Step 4: back to mu.
  have hmble2 : Measurable fun omega => ENNReal.ofReal (qr * (2 * g omega) ^ (p - 1)) :=
    ((measurable_const.mul ((measurable_const.mul hgmble).pow_const _)).ennreal_ofReal)
  have hnuint : ∫⁻ omega, ENNReal.ofReal (qr * (2 * g omega) ^ (p - 1)) ∂nu
      = ∫⁻ omega, ENNReal.ofReal (g omega) *
          ENNReal.ofReal (qr * (2 * g omega) ^ (p - 1)) ∂mu := by
    rw [hnudef, lintegral_withDensity_eq_lintegral_mul mu hgenn hmble2]
    simp only [Pi.mul_apply]
  have hpointwise : ∀ omega, ENNReal.ofReal (g omega) *
        ENNReal.ofReal (qr * (2 * g omega) ^ (p - 1))
      = ENNReal.ofReal (qr * 2 ^ (p - 1)) * ENNReal.ofReal (g omega ^ p) := by
    intro omega
    have hgn := hgnn omega
    rw [← ENNReal.ofReal_mul hgn, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hsucc : p - 1 + 1 = p := by omega
    have hpow : g omega ^ (p - 1) * g omega = g omega ^ p := by
      rw [← pow_succ, hsucc]
    calc g omega * (qr * (2 * g omega) ^ (p - 1))
        = qr * 2 ^ (p - 1) * (g omega ^ (p - 1) * g omega) := by
          rw [mul_pow]; ring
      _ = qr * 2 ^ (p - 1) * g omega ^ p := by rw [hpow]
  -- Step 5: assembling.
  have hmain : ∫⁻ omega, ENNReal.ofReal (S omega ^ p) ∂mu
      ≤ 2 * (ENNReal.ofReal (qr * 2 ^ (p - 1)) *
          ∫⁻ omega, ENNReal.ofReal (g omega ^ p) ∂mu) := by
    rw [hlayer1]
    have hint : ∫⁻ t in Set.Ioi (0 : ℝ), mu {omega | t ≤ S omega} *
          ENNReal.ofReal ((p : ℝ) * t ^ (p - 1))
        ≤ ∫⁻ t in Set.Ioi (0 : ℝ), 2 * (nu {omega | t ≤ 2 * g omega} *
            ENNReal.ofReal ((p : ℝ) * t ^ (p - 2))) := by
      refine setLIntegral_mono' measurableSet_Ioi ?_
      intro t ht
      have htpos : (0 : ℝ) < t := ht
      have hsplitpow : ENNReal.ofReal ((p : ℝ) * t ^ (p - 1))
          = ENNReal.ofReal ((p : ℝ) * t ^ (p - 2)) * ENNReal.ofReal t := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have hsucc : p - 2 + 1 = p - 1 := by omega
        calc (p : ℝ) * t ^ (p - 1) = (p : ℝ) * (t ^ (p - 2) * t) := by
              rw [← pow_succ, hsucc]
          _ = (p : ℝ) * t ^ (p - 2) * t := by ring
      rw [hsplitpow]
      calc mu {omega | t ≤ S omega} *
            (ENNReal.ofReal ((p : ℝ) * t ^ (p - 2)) * ENNReal.ofReal t)
          = ENNReal.ofReal ((p : ℝ) * t ^ (p - 2)) *
              (ENNReal.ofReal t * mu {omega | t ≤ S omega}) := by ring
        _ ≤ ENNReal.ofReal ((p : ℝ) * t ^ (p - 2)) *
              (2 * nu {omega | t ≤ 2 * g omega}) :=
            mul_le_mul_right (hsplit t htpos) _
        _ = 2 * (nu {omega | t ≤ 2 * g omega} *
              ENNReal.ofReal ((p : ℝ) * t ^ (p - 2))) := by ring
    refine le_trans hint ?_
    rw [lintegral_const_mul' 2 _ (by norm_num), hlayer2, hnuint]
    refine mul_le_mul_right ?_ 2
    rw [lintegral_congr hpointwise, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine le_trans hmain ?_
  rw [← mul_assoc, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  refine mul_le_mul_left (le_of_eq ?_) _
  congr 1
  have hsucc : p - 1 + 1 = p := by omega
  calc (2 : ℝ) * (qr * 2 ^ (p - 1)) = qr * (2 ^ (p - 1) * 2) := by ring
    _ = qr * 2 ^ p := by rw [← pow_succ, hsucc]
    _ = 2 ^ p * qr := by ring

end SubdiffusiveProcess
