import SubdiffusiveProcess.Static.Comparison
import SubdiffusiveProcess.Frozen.Section6.Defs.CoefficientAt
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.GoodSetMeasurable
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellSummable

/-! # The three literal clauses of the local static estimate -/

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- Positive and negative mass growth on all subscale balls. -/
def localMassEstimates {d : ℕ} (b : Vec d → ℝ) (y0 : Vec d) (ρ0 K : ℝ) : Prop :=
  ∀ (x : Vec d) (r : ℝ), 0 < r → r ≤ 1 → Metric.ball x r ⊆ Metric.ball y0 (ρ0 / 2) →
      ENNReal.ofReal (K⁻¹ * r ^ ((d : ℝ) + 1 / 2)) ≤
          volume.withDensity (fun z => ENNReal.ofReal (b z)) (Metric.ball x r) ∧
        volume.withDensity (fun z => ENNReal.ofReal (b z)) (Metric.ball x r) ≤
          ENNReal.ofReal (K * r ^ ((d : ℝ) - 1 / 2))

/-- Both native Sobolev coercivity inequalities on the dyadic nested family. -/
def localCoercivityEstimates {d : ℕ} (A : Vec d → ℝ) {p : ℕ}
    (c : Fin p → Vec d) (s0 s1 : Fin p → ℝ) (K B : ℝ) : Prop :=
  ∀ (i : Fin p) (n k : ℕ), k ≤ 2 ^ n →
      (∀ v : Homogenization.H1Function
            (Metric.ball (c i) (((1 - (k : ℝ) / 2 ^ n) * s0 i + ((k : ℝ) / 2 ^ n) * s1 i) / 2)),
        (∫⁻ x in Metric.ball (c i) (((1 - (k : ℝ) / 2 ^ n) * s0 i + ((k : ℝ) / 2 ^ n) * s1 i) / 2),
            ∫⁻ z in Metric.ball (c i) (((1 - (k : ℝ) / 2 ^ n) * s0 i + ((k : ℝ) / 2 ^ n) * s1 i) / 2),
              ENNReal.ofReal ((v.toFun x - v.toFun z) ^ 2) /
                ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))) +
          ∫⁻ x in Metric.ball (c i) (((1 - (k : ℝ) / 2 ^ n) * s0 i + ((k : ℝ) / 2 ^ n) * s1 i) / 2),
            ENNReal.ofReal (v.toFun x ^ 2) ≤
        ENNReal.ofReal (K * (2 : ℝ) ^ (B * n)) *
          ((∫⁻ x in Metric.ball (c i) (((1 - (k : ℝ) / 2 ^ n) * s0 i + ((k : ℝ) / 2 ^ n) * s1 i) / 2),
              ENNReal.ofReal (A x * Homogenization.vecDot (v.grad x) (v.grad x))) +
            ∫⁻ x in Metric.ball (c i) (((1 - (k : ℝ) / 2 ^ n) * s0 i + ((k : ℝ) / 2 ^ n) * s1 i) / 2),
              ENNReal.ofReal (v.toFun x ^ 2))) ∧
      (∀ v : Homogenization.H10Function
            (Metric.ball (c i) (((1 - (k : ℝ) / 2 ^ n) * s0 i + ((k : ℝ) / 2 ^ n) * s1 i) / 2)),
        (∫⁻ x in Metric.ball (c i) (((1 - (k : ℝ) / 2 ^ n) * s0 i + ((k : ℝ) / 2 ^ n) * s1 i) / 2),
            ∫⁻ z in Metric.ball (c i) (((1 - (k : ℝ) / 2 ^ n) * s0 i + ((k : ℝ) / 2 ^ n) * s1 i) / 2),
              ENNReal.ofReal ((v.toFun x - v.toFun z) ^ 2) /
                ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))) +
          ∫⁻ x in Metric.ball (c i) (((1 - (k : ℝ) / 2 ^ n) * s0 i + ((k : ℝ) / 2 ^ n) * s1 i) / 2),
            ENNReal.ofReal (v.toFun x ^ 2) ≤
        ENNReal.ofReal (K * (2 : ℝ) ^ (B * n)) *
          ∫⁻ x in Metric.ball (c i) (((1 - (k : ℝ) / 2 ^ n) * s0 i + ((k : ℝ) / 2 ^ n) * s1 i) / 2),
            ENNReal.ofReal (A x * Homogenization.vecDot (v.grad x) (v.grad x)))

/-- Native harmonic cutoff witnesses with all-radius energy growth. -/
def localHarmonicCutoffEstimates {d : ℕ} (A : Vec d → ℝ) {p : ℕ}
    (c : Fin p → Vec d) (s0 s1 : Fin p → ℝ) (K B : ℝ) : Prop :=
  ∀ (i : Fin p) (n k : ℕ), k < 2 ^ n →
      ∃ chi : Homogenization.H10Function
          (Metric.ball (c i) (((1 - ((k + 1 : ℕ) : ℝ) / 2 ^ n) * s0 i +
            (((k + 1 : ℕ) : ℝ) / 2 ^ n) * s1 i) / 2)),
        (∀ x, 0 ≤ chi.toFun x ∧ chi.toFun x ≤ 1) ∧
        (∀ x ∈ Metric.ball (c i) (((1 - (k : ℝ) / 2 ^ n) * s0 i + ((k : ℝ) / 2 ^ n) * s1 i) / 2),
          chi.toFun x = 1) ∧
        tsupport chi.toFun ⊆ Metric.ball (c i) (((1 - ((k + 1 : ℕ) : ℝ) / 2 ^ n) * s0 i +
            (((k + 1 : ℕ) : ℝ) / 2 ^ n) * s1 i) / 2) ∧
        ∀ (x : Vec d) (r : ℝ), 0 < r → r ≤ 1 →
          ∫⁻ z in Metric.ball x r ∩ Metric.ball (c i) (((1 - ((k + 1 : ℕ) : ℝ) / 2 ^ n) * s0 i +
              (((k + 1 : ℕ) : ℝ) / 2 ^ n) * s1 i) / 2),
              ENNReal.ofReal (A z * Homogenization.vecDot (chi.grad z) (chi.grad z)) ≤
            ENNReal.ofReal (K * ((s1 i - s0 i) / 2 ^ n / 2) ^ (-B) * r ^ ((d : ℝ) - 1 / 2))

/-- The separate suppliers assemble into the exact original predicate. -/
theorem estimates_iff_clauses {d : ℕ} (b A : Vec d → ℝ) (y0 : Vec d) (ρ0 : ℝ) {p : ℕ}
    (c : Fin p → Vec d) (s0 s1 : Fin p → ℝ) (K B : ℝ) :
    SubdiffusiveProcess.Static.estimates b A y0 ρ0 c s0 s1 K B ↔
      localMassEstimates b y0 ρ0 K ∧ localCoercivityEstimates A c s0 s1 K B ∧
        localHarmonicCutoffEstimates A c s0 s1 K B := Iff.rfl

end SubdiffusiveProcess.Static
