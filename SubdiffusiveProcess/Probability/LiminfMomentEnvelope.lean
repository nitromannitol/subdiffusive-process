module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.Tactic

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace SubdiffusiveProcess.Probability

/-- The finite real representative of the lower limit of the samplewise norms. -/
def liminfEnvelope {X : Type*} (f : ℕ → X → ℝ) (x : X) : ℝ :=
  (liminf (fun n => ‖f n x‖ₑ) atTop).toReal

theorem measurable_liminfEnvelope {X : Type*} [MeasurableSpace X]
    (f : ℕ → X → ℝ) (hf : ∀ n, Measurable (f n)) :
    Measurable (liminfEnvelope f) :=
  (Measurable.liminf (fun n => (hf n).enorm)).ennreal_toReal

theorem liminfEnvelope_nonneg {X : Type*} (f : ℕ → X → ℝ) (x : X) :
    0 ≤ liminfEnvelope f x := ENNReal.toReal_nonneg

/-- Fatou retains each positive moment of a uniformly bounded family. -/
theorem eLpNorm_liminfEnvelope_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : ℕ → X → ℝ) (hf : ∀ n, Measurable (f n))
    (q B : ℝ) (hq : 0 < q) (hB : 0 ≤ B)
    (hb : ∀ n, eLpNorm (f n) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B) :
    eLpNorm (liminfEnvelope f) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B := by
  have hq0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
  have hqtop : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpow : ∀ x, (‖liminfEnvelope f x‖ₑ) ^ q ≤
      liminf (fun n => (‖f n x‖ₑ) ^ q) atTop := by
    intro x
    have henv : ‖liminfEnvelope f x‖ₑ ≤ liminf (fun n => ‖f n x‖ₑ) atTop := by
      rw [Real.enorm_eq_ofReal (liminfEnvelope_nonneg f x)]
      exact ENNReal.ofReal_toReal_le
    have hcomm : (liminf (fun n => ‖f n x‖ₑ) atTop) ^ q =
        liminf (fun n => (‖f n x‖ₑ) ^ q) atTop := by
      change ENNReal.orderIsoRpow q hq (liminf (fun n => ‖f n x‖ₑ) atTop) =
        liminf (fun n => ENNReal.orderIsoRpow q hq (‖f n x‖ₑ)) atTop
      refine OrderIso.liminf_apply _ ?_ ?_ ?_ ?_ <;> isBoundedDefault
    exact (ENNReal.rpow_le_rpow henv hq.le).trans_eq hcomm
  have hint : ∫⁻ x, (‖liminfEnvelope f x‖ₑ) ^ q ∂μ ≤ (ENNReal.ofReal B) ^ q := by
    refine (lintegral_mono hpow).trans
      ((lintegral_liminf_le (fun n => (hf n).enorm.pow_const q)).trans ?_)
    apply liminf_le_of_frequently_le'
    apply Frequently.of_forall
    intro n
    have h := hb n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop (hf n).aestronglyMeasurable,
      ENNReal.toReal_ofReal hq.le, one_div] at h
    exact (ENNReal.rpow_inv_le_iff hq).1 h
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop
    (measurable_liminfEnvelope f hf).aestronglyMeasurable,
    ENNReal.toReal_ofReal hq.le, one_div]
  exact (ENNReal.rpow_inv_le_iff hq).2 hint

theorem memLp_liminfEnvelope {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : ℕ → X → ℝ) (hf : ∀ n, Measurable (f n))
    (q B : ℝ) (hq : 0 < q) (hB : 0 ≤ B)
    (hb : ∀ n, eLpNorm (f n) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B) :
    MemLp (liminfEnvelope f) (ENNReal.ofReal q) μ :=
  (eLpNorm_liminfEnvelope_le μ f hf q B hq hB hb).trans_lt ENNReal.ofReal_lt_top

/-- Infinitely many input norms lie within one of the finite lower envelope. -/
theorem frequently_norm_lt_liminfEnvelope_add_one {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : ℕ → X → ℝ) (hf : ∀ n, Measurable (f n))
    (q B : ℝ) (hq : 0 < q) (hB : 0 ≤ B)
    (hb : ∀ n, eLpNorm (f n) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B) :
    ∀ᵐ x ∂μ, ∃ᶠ n in atTop, ‖f n x‖ < liminfEnvelope f x + 1 := by
  have hfinite := ae_bdd_liminf_atTop_of_eLpNorm_bdd (f := f) (μ := μ)
    ((ENNReal.ofReal_pos.mpr hq).ne')
    (R := ⟨B, hB⟩) (fun n => (hb n).trans_eq (ENNReal.ofReal_eq_coe_nnreal hB))
  filter_upwards [hfinite] with x hx
  have henv0 := liminfEnvelope_nonneg f x
  have hlt : liminf (fun n => ‖f n x‖ₑ) atTop <
      ENNReal.ofReal (liminfEnvelope f x + 1) := by
    rw [← ENNReal.ofReal_toReal hx.ne, liminfEnvelope]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (lt_add_one _)
  have hfr := frequently_lt_of_liminf_lt (by isBoundedDefault) hlt
  refine hfr.mono fun n hn => ?_
  rw [← ofReal_norm] at hn
  exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hn


/-- A product of two order-q variables has order q/2. -/
theorem memLp_mul_half {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} (q : ℝ) (hq : 0 < q)
    (hf : MemLp f (ENNReal.ofReal q) μ) (hg : MemLp g (ENNReal.ofReal q) μ) :
    MemLp (fun x => f x * g x) (ENNReal.ofReal (q / 2)) μ := by
  letI : ENNReal.HolderTriple (ENNReal.ofReal q) (ENNReal.ofReal q)
      (ENNReal.ofReal (q / 2)) := by
    constructor
    rw [← ENNReal.ofReal_inv_of_pos hq, ← ENNReal.ofReal_inv_of_pos (half_pos hq),
      ← ENNReal.ofReal_add (inv_nonneg.mpr hq.le) (inv_nonneg.mpr hq.le)]
    congr 1
    field_simp
    ring
  exact hf.fun_mul (r := ENNReal.ofReal (q / 2)) hg


/-- Uniform moments give an integer level with infinitely many simultaneously bounded inputs;
the level lies within two of a measurable envelope with all prescribed moments. -/
theorem exists_common_level_envelope {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ps : Finset ℝ) (hps : ps.Nonempty)
    (hp : ∀ q ∈ ps, (1 : ℝ) ≤ q) (k h : ℕ → X → ℝ)
    (hk : ∀ n, Measurable (k n)) (hh : ∀ n, Measurable (h n))
    (hn : ∀ᵐ x ∂μ, ∀ n, 0 ≤ k n x ∧ 0 ≤ h n x)
    (hm : ∀ q ∈ ps, (∃ B : ℝ, ∀ n,
      (eLpNorm (k n) (ENNReal.ofReal q) μ).toReal ≤ B ∧
      (eLpNorm (h n) (ENNReal.ofReal q) μ).toReal ≤ B) ∧
      ∀ n, MemLp (k n) (ENNReal.ofReal q) μ ∧ MemLp (h n) (ENNReal.ofReal q) μ) :
    ∃ E : X → ℝ, Measurable E ∧ (∀ x, 0 ≤ E x) ∧
      (∀ q ∈ ps, MemLp E (ENNReal.ofReal q) μ) ∧
      ∀ᵐ x ∂μ, ∃ b : ℕ, (b : ℝ) ≤ E x + 2 ∧
        ∃ᶠ n in atTop, k n x ≤ b ∧ h n x ≤ b := by
  let f : ℕ → X → ℝ := fun n x => k n x + h n x
  have hf : ∀ n, Measurable (f n) := fun n => (hk n).add (hh n)
  have hb : ∀ q ∈ ps, ∃ B : ℝ, 0 ≤ B ∧
      ∀ n, eLpNorm (f n) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B := by
    intro q hq
    obtain ⟨B, hB⟩ := (hm q hq).1
    have hB0 : 0 ≤ B := ENNReal.toReal_nonneg.trans (hB 0).1
    refine ⟨2 * B, by positivity, fun n => ?_⟩
    have hkB : eLpNorm (k n) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B := by
      rw [← ENNReal.ofReal_toReal ((hm q hq).2 n).1.ne]
      exact ENNReal.ofReal_le_ofReal (hB n).1
    have hhB : eLpNorm (h n) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B := by
      rw [← ENNReal.ofReal_toReal ((hm q hq).2 n).2.ne]
      exact ENNReal.ofReal_le_ofReal (hB n).2
    refine (eLpNorm_add_le (f := k n) (g := h n)
      (by exact_mod_cast (ENNReal.ofReal_le_ofReal (hp q hq)))).trans ?_
    calc
      eLpNorm (k n) (ENNReal.ofReal q) μ + eLpNorm (h n) (ENNReal.ofReal q) μ ≤
          ENNReal.ofReal B + ENNReal.ofReal B := add_le_add hkB hhB
      _ = ENNReal.ofReal (2 * B) := by rw [← ENNReal.ofReal_add hB0 hB0]; congr 1; ring
  let E := liminfEnvelope f
  have hE : ∀ x, 0 ≤ E x := liminfEnvelope_nonneg f
  refine ⟨E, measurable_liminfEnvelope f hf, hE, ?_, ?_⟩
  · intro q hq
    obtain ⟨B, hB0, hB⟩ := hb q hq
    exact memLp_liminfEnvelope μ f hf q B (lt_of_lt_of_le zero_lt_one (hp q hq)) hB0 hB
  · obtain ⟨q, hq⟩ := hps
    obtain ⟨B, hB0, hB⟩ := hb q hq
    have hfr := frequently_norm_lt_liminfEnvelope_add_one μ f hf q B
      (lt_of_lt_of_le zero_lt_one (hp q hq)) hB0 hB
    filter_upwards [hfr, hn] with x hx hnx
    refine ⟨⌈E x + 1⌉₊, ?_, hx.mono fun n hn => ?_⟩
    · exact (Nat.ceil_lt_add_one (by linarith [hE x])).le.trans_eq (by ring)
    · rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (hnx n).1 (hnx n).2)] at hn
      have hsum : k n x + h n x ≤ (⌈E x + 1⌉₊ : ℝ) := hn.le.trans (Nat.le_ceil _)
      exact ⟨by linarith [(hnx n).2], by linarith [(hnx n).1]⟩

end SubdiffusiveProcess.Probability
