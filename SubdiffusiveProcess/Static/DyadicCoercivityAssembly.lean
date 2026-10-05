module

public import SubdiffusiveProcess.Static.DyadicMajorant
public import SubdiffusiveProcess.Static.LocalEstimateClauses

@[expose] public section

/-! # Dyadic assembly of individual native coercivity estimates -/

open MeasureTheory Homogenization
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- Both native coercivity inequalities on one cube. -/
def cubeCoercivityEstimates {d : ℕ} (A : Vec d → ℝ) (y : Vec d) (s K : ℝ) : Prop :=
  (∀ v : H1Function (Metric.ball y (s / 2)),
    SubdiffusiveProcess.Static.fractionalSqNorm (Metric.ball y (s / 2)) v.toFun ≤
      ENNReal.ofReal K *
        (SubdiffusiveProcess.Static.energy (Metric.ball y (s / 2)) A v.grad +
          ∫⁻ x in Metric.ball y (s / 2), ENNReal.ofReal (v.toFun x ^ 2))) ∧
  (∀ v : H10Function (Metric.ball y (s / 2)),
    SubdiffusiveProcess.Static.fractionalSqNorm (Metric.ball y (s / 2)) v.toFun ≤
      ENNReal.ofReal K * SubdiffusiveProcess.Static.energy (Metric.ball y (s / 2)) A v.grad)

/-- A uniformly bounded measurable bank of individual cube constants gives
one static coercivity constant, with the fixed exponent five. -/
theorem exists_dyadic_coercivity_constant {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d p : ℕ}
    (A : Ω → Vec d → ℝ) (c : Fin p → Vec d) (s0 s1 : Fin p → ℝ)
    {q B : ℝ} (hq : 1 ≤ q) (hB : 0 ≤ B)
    (Z : ∀ n : ℕ, Fin p → Fin (2 ^ n + 1) → Ω → ℝ)
    (hZ : ∀ n i k, AEStronglyMeasurable (Z n i k) μ)
    (hnorm : ∀ n i k, eLpNorm (Z n i k) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B)
    (hcoer : ∀ (n : ℕ) (i : Fin p) (k : Fin (2 ^ n + 1)), ∀ᵐ ω ∂μ,
      cubeCoercivityEstimates (A ω) (c i)
        ((1 - ((k : ℕ) : ℝ) / 2 ^ n) * s0 i + (((k : ℕ) : ℝ) / 2 ^ n) * s1 i)
        (Z n i k ω)) :
    ∃ K : Ω → ℝ, Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
      (∫⁻ ω, ENNReal.ofReal (K ω ^ q) ∂μ) ≤
        ENNReal.ofReal ((1 + 4 * (p : ℝ) * B) ^ q) ∧
      ∀ᵐ ω ∂μ, localCoercivityEstimates (A ω) c s0 s1 (K ω) 5 := by
  obtain ⟨K, hK, hK1, hKmom, hmajor⟩ :=
    exists_dyadic_majorant μ p hq hB Z hZ hnorm
  have hall : ∀ᵐ ω ∂μ, ∀ (n : ℕ) (i : Fin p) (k : Fin (2 ^ n + 1)), _ :=
    (ae_all_iff.mpr fun n => ae_all_iff.mpr fun i => ae_all_iff.mpr fun k => hcoer n i k)
  refine ⟨K, hK, hK1, hKmom, ?_⟩
  filter_upwards [hmajor, hall] with ω hω hωcoer
  intro i n k hk
  let k' : Fin (2 ^ n + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
  have hgrowth : (2 : ℝ) ^ (2 * n) ≤ (2 : ℝ) ^ (5 * (n : ℝ)) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hZfac : ENNReal.ofReal (Z n i k' ω) ≤
      ENNReal.ofReal (K ω * (2 : ℝ) ^ (5 * (n : ℝ))) := by
    apply ENNReal.ofReal_le_ofReal
    exact ((le_abs_self _).trans (hω n i k')).trans
      (mul_le_mul_of_nonneg_left hgrowth (zero_le_one.trans (hK1 ω)))
  obtain ⟨h1, h10⟩ := hωcoer n i k'
  constructor
  · intro v
    exact (h1 v).trans (mul_le_mul_left hZfac _)
  · intro v
    exact (h10 v).trans (mul_le_mul_left hZfac _)

end SubdiffusiveProcess.Static
