module

public import SubdiffusiveProcess.Section10.KilledSobolevConstants
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

@[expose] public section




open MeasureTheory
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Section10

/-- Static moment order sufficient for the requested Sobolev moment. -/
def killedSobolevMomentOrder (q : ℝ) : ℝ := max 1 (2 * q)

lemma killedSobolevMomentOrder_ge_one (q : ℝ) :
    1 ≤ killedSobolevMomentOrder q := le_max_left _ _

lemma two_mul_le_killedSobolevMomentOrder (q : ℝ) :
    2 * q ≤ killedSobolevMomentOrder q := le_max_right _ _

/-- The bank constant is at least one on every sample, including the exceptional set. -/
def killedSobolevBankConstant (D k : ℝ) : ℝ := max 1 (D * k ^ 2)

lemma killedSobolevBankConstant_ge_one (D k : ℝ) :
    1 ≤ killedSobolevBankConstant D k := le_max_left _ _

lemma mul_sq_le_killedSobolevBankConstant (D k : ℝ) :
    D * k ^ 2 ≤ killedSobolevBankConstant D k := le_max_right _ _

lemma measurable_killedSobolevBankConstant {Ω : Type*} [MeasurableSpace Ω]
    {K : Ω → ℝ} (hK : Measurable K) (D : ℝ) :
    Measurable (fun ω => killedSobolevBankConstant D (K ω)) :=
  measurable_const.max (measurable_const.mul (hK.pow_const 2))

/-- Positive moments of the transformed bank use the static order `max 1 (2*q)`. -/
lemma killedSobolevBankConstant_rpow_le {D k q : ℝ}
    (hD : 0 ≤ D) (hk : 1 ≤ k) (hq : 0 ≤ q) :
    killedSobolevBankConstant D k ^ q ≤
      1 + D ^ q * k ^ killedSobolevMomentOrder q := by
  have hk0 : 0 ≤ k := zero_le_one.trans hk
  have hp : (D * k ^ 2) ^ q = D ^ q * k ^ (2 * q) := by
    rw [Real.mul_rpow hD (sq_nonneg k), ← Real.rpow_natCast_mul hk0 2 q]
    norm_num
  rw [killedSobolevBankConstant, Real.rpow_max zero_le_one (mul_nonneg hD (sq_nonneg k)) hq,
    Real.one_rpow, hp]
  have hpow : k ^ (2 * q) ≤ k ^ killedSobolevMomentOrder q :=
    Real.rpow_le_rpow_of_exponent_le hk (two_mul_le_killedSobolevMomentOrder q)
  have hm := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hD q)
  exact max_le (le_add_of_nonneg_right
    (mul_nonneg (Real.rpow_nonneg hD q) (Real.rpow_nonneg hk0 _)))
    (hm.trans (le_add_of_nonneg_left zero_le_one))

/-- Nonpositive moments cost at most one, since the bank constant is everywhere ≥1. -/
lemma killedSobolevBankConstant_rpow_le_one {D k q : ℝ} (hq : q ≤ 0) :
    killedSobolevBankConstant D k ^ q ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (killedSobolevBankConstant_ge_one D k) hq

/-- Combine two genuine moment suppliers without changing their moment order. -/
lemma lintegral_max_rpow_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {f g : Ω → ℝ} {q Cf Cg : ℝ} (hf : Measurable f)
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) (hq : 0 ≤ q)
    (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hmf : (∫⁻ ω, ENNReal.ofReal (f ω ^ q) ∂P) ≤ ENNReal.ofReal Cf)
    (hmg : (∫⁻ ω, ENNReal.ofReal (g ω ^ q) ∂P) ≤ ENNReal.ofReal Cg) :
    (∫⁻ ω, ENNReal.ofReal (max (f ω) (g ω) ^ q) ∂P) ≤ ENNReal.ofReal (Cf + Cg) := by
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (f ω ^ q) + ENNReal.ofReal (g ω ^ q) ∂P := by
      apply lintegral_mono
      intro ω
      change ENNReal.ofReal (max (f ω) (g ω) ^ q) ≤
        ENNReal.ofReal (f ω ^ q) + ENNReal.ofReal (g ω ^ q)
      rw [Real.rpow_max (hf0 ω) (hg0 ω) hq,
        ← ENNReal.ofReal_add (Real.rpow_nonneg (hf0 ω) q) (Real.rpow_nonneg (hg0 ω) q)]
      exact ENNReal.ofReal_le_ofReal
        (max_le (le_add_of_nonneg_right (Real.rpow_nonneg (hg0 ω) q))
          (le_add_of_nonneg_left (Real.rpow_nonneg (hf0 ω) q)))
    _ = (∫⁻ ω, ENNReal.ofReal (f ω ^ q) ∂P) +
        (∫⁻ ω, ENNReal.ofReal (g ω ^ q) ∂P) :=
      lintegral_add_left (ENNReal.measurable_ofReal.comp (hf.pow measurable_const)) _
    _ ≤ ENNReal.ofReal Cf + ENNReal.ofReal Cg := add_le_add hmf hmg
    _ = ENNReal.ofReal (Cf + Cg) := (ENNReal.ofReal_add hCf hCg).symm

/-- Transfer a genuine lower-integral moment on a probability law. For positive
q the deterministic bound is `1 + D^q*C`; for nonpositive q it is one. -/
theorem killedSobolevBankConstant_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {K : Ω → ℝ} {D C q : ℝ}
    (hK : Measurable K) (hKone : ∀ ω, 1 ≤ K ω) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hmoment : (∫⁻ ω, ENNReal.ofReal (K ω ^ killedSobolevMomentOrder q) ∂P) ≤
      ENNReal.ofReal C) :
    (∫⁻ ω, ENNReal.ofReal (killedSobolevBankConstant D (K ω) ^ q) ∂P) ≤
      ENNReal.ofReal (if 0 < q then 1 + D ^ q * C else 1) := by
  split_ifs with hq
  · calc
      _ ≤ ∫⁻ ω, ENNReal.ofReal (1 + D ^ q * K ω ^ killedSobolevMomentOrder q) ∂P :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal
          (killedSobolevBankConstant_rpow_le hD (hKone ω) hq.le)
      _ = 1 + ENNReal.ofReal (D ^ q) *
          (∫⁻ ω, ENNReal.ofReal (K ω ^ killedSobolevMomentOrder q) ∂P) := by
        simp_rw [ENNReal.ofReal_add zero_le_one
          (mul_nonneg (Real.rpow_nonneg hD q)
            (Real.rpow_nonneg (zero_le_one.trans (hKone _)) _)),
          ENNReal.ofReal_mul (Real.rpow_nonneg hD q), ENNReal.ofReal_one]
        rw [lintegral_add_left measurable_const, lintegral_const_mul]
        · simp
        · exact ENNReal.measurable_ofReal.comp (hK.pow measurable_const)
      _ ≤ 1 + ENNReal.ofReal (D ^ q) * ENNReal.ofReal C := by gcongr
      _ = ENNReal.ofReal (1 + D ^ q * C) := by
        rw [ENNReal.ofReal_add zero_le_one (mul_nonneg (Real.rpow_nonneg hD q) hC),
          ENNReal.ofReal_one, ENNReal.ofReal_mul (Real.rpow_nonneg hD q)]
  · calc
      _ ≤ ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂P := lintegral_mono fun ω => by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
          (killedSobolevBankConstant_rpow_le_one (le_of_not_gt hq) (D := D) (k := K ω))
      _ = ENNReal.ofReal 1 := by simp

end SubdiffusiveProcess.Section10
