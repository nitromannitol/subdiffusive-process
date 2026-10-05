module

public import SubdiffusiveProcess.Probability.CountableEnvelope
@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace SubdiffusiveProcess

/-- Geometric Lp bounds on actual Banach-valued increments give almost-sure absolute summability and the exact geometric Lp bound for every literal series tail. No independence or tail bound is assumed. -/
theorem memLp_geometric_tsum_tails
    {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [CompleteSpace E]
    (μ : Measure X) [IsProbabilityMeasure μ]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (_hpt : p ≠ ∞)
    (F : ℕ → X → E) (hF : ∀ n, MemLp (F n) p μ)
    {B r : ℝ} (hB : 0 ≤ B) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hbound : ∀ n, eLpNorm (F n) p μ ≤ ENNReal.ofReal (B * r ^ n)) :
    (∀ᵐ x ∂μ, Summable (fun n => ‖F n x‖)) ∧
    (∀ H : ℕ,
      MemLp (fun x => ∑' n : ℕ, F (n + H) x) p μ ∧
      eLpNorm (fun x => ∑' n : ℕ, F (n + H) x) p μ ≤
        ENNReal.ofReal (B * r ^ H / (1 - r))) := by
  have hInt : ∀ n, Integrable (F n) μ := fun n => (hF n).integrable hp
  have hInt_le : ∀ n, ∫ x, ‖F n x‖ ∂μ ≤ B * r ^ n := by
    intro n
    calc
      ∫ x, ‖F n x‖ ∂μ = (eLpNorm (F n) 1 μ).toReal := by
        rw [eLpNorm_one_eq_lintegral_enorm (hF n).aestronglyMeasurable, integral_norm_eq_lintegral_enorm (hF n).aestronglyMeasurable]
      _ ≤ (eLpNorm (F n) p μ).toReal := ENNReal.toReal_mono (hF n).ne
        (eLpNorm_le_eLpNorm_of_exponent_le hp)
      _ ≤ (ENNReal.ofReal (B * r ^ n)).toReal := ENNReal.toReal_mono
        ENNReal.ofReal_ne_top (hbound n)
      _ = B * r ^ n := ENNReal.toReal_ofReal (mul_nonneg hB (pow_nonneg hr0 n))
  have hsGeom : Summable (fun n : ℕ => B * r ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left B
  have hsInt : Summable (fun n => ∫ x, ‖F n x‖ ∂μ) :=
    Summable.of_nonneg_of_le
      (fun n => integral_nonneg (fun x => norm_nonneg (F n x))) hInt_le hsGeom
  have hPoint : ∀ᵐ x ∂μ, Summable (fun n => ‖F n x‖) :=
    ae_summable_norm_of_summable_integral_norm hInt hsInt
  refine ⟨hPoint, ?_⟩
  intro H
  let S : ℕ → X → E := fun N => ∑ n ∈ Finset.range N, F (n + H)
  have hFiniteBound : ∀ N, eLpNorm (S N) p μ ≤
      ENNReal.ofReal (B * r ^ H / (1 - r)) := by
    intro N
    have hmink : eLpNorm (∑ n ∈ Finset.range N, fun x => F (n + H) x) p μ ≤
        ∑ n ∈ Finset.range N, eLpNorm (F (n + H)) p μ :=
      eLpNorm_sum_le (p := p) (μ := μ) (s := Finset.range N)
        (f := fun n x => F (n + H) x) hp
    have hterms : (∑ n ∈ Finset.range N, eLpNorm (F (n + H)) p μ) ≤
        ∑ n ∈ Finset.range N, ENNReal.ofReal (B * r ^ (n + H)) :=
      Finset.sum_le_sum fun n hn => hbound (n + H)
    have hofReal : (∑ n ∈ Finset.range N, ENNReal.ofReal (B * r ^ (n + H))) =
        ENNReal.ofReal (∑ n ∈ Finset.range N, B * r ^ (n + H)) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro n hn
      exact mul_nonneg hB (pow_nonneg hr0 _)
    have hreal : (∑ n ∈ Finset.range N, B * r ^ (n + H)) ≤
        B * r ^ H / (1 - r) := by
      calc
        ∑ n ∈ Finset.range N, B * r ^ (n + H)
            = B * r ^ H * ∑ n ∈ Finset.range N, r ^ n := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro n hn
                rw [pow_add]
                ring
        _ ≤ B * r ^ H * ∑' n : ℕ, r ^ n := by
          gcongr
          exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _
            (fun n hn => pow_nonneg hr0 n)
        _ = B * r ^ H / (1 - r) := by
          rw [tsum_geometric_of_lt_one hr0 hr1]
          field_simp
    calc
      eLpNorm (S N) p μ ≤ ∑ n ∈ Finset.range N, eLpNorm (F (n + H)) p μ := by
        exact hmink
      _ ≤ ∑ n ∈ Finset.range N, ENNReal.ofReal (B * r ^ (n + H)) := hterms
      _ = ENNReal.ofReal (∑ n ∈ Finset.range N, B * r ^ (n + H)) := hofReal
      _ ≤ ENNReal.ofReal (B * r ^ H / (1 - r)) := ENNReal.ofReal_le_ofReal hreal
  have hTendsto : ∀ᵐ x ∂μ,
      Tendsto (fun N => S N x) atTop (𝓝 (∑' n : ℕ, F (n + H) x)) := by
    filter_upwards [hPoint] with x hx
    have hs : Summable (fun n => F (n + H) x) :=
      (hx.of_norm).comp_injective (fun _ _ h => Nat.add_right_cancel h)
    simpa only [S, Finset.sum_apply] using hs.hasSum.tendsto_sum_nat
  have hMeas : ∀ N, AEStronglyMeasurable (S N) μ := fun N =>
    (memLp_finsetSum' (Finset.range N) fun n hn => hF (n + H)).aestronglyMeasurable
  have hLimitMeas : AEStronglyMeasurable (fun x => ∑' n : ℕ, F (n + H) x) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hMeas hTendsto
  have hLimitBound : eLpNorm (fun x => ∑' n : ℕ, F (n + H) x) p μ ≤
      ENNReal.ofReal (B * r ^ H / (1 - r)) :=
    Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall hFiniteBound) hMeas hLimitMeas hTendsto
  have hRhsTop : ENNReal.ofReal (B * r ^ H / (1 - r)) < ∞ := by simp
  exact ⟨hLimitBound.trans_lt hRhsTop, hLimitBound⟩

end SubdiffusiveProcess
