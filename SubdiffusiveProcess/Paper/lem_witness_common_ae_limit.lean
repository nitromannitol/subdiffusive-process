module

public import SubdiffusiveProcess.Paper.lem_band
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

lemma aux_ae_tendsto_zero_of_eLpNorm_rpow_tsum
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    (p : ℝ) (hp : 0 < p)
    (f : ℕ → Ω → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) P)
    (hsum :
      (∑' n : ℕ, eLpNorm (f n) (ENNReal.ofReal p) P ^ p) ≠ ∞) :
    ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (0 : ℝ)) := by
  have hp0 : ENNReal.ofReal p ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hp).ne'
  have hp_top : ENNReal.ofReal p ≠ ∞ :=
    ENNReal.ofReal_ne_top
  have hpow (n : ℕ) :
      (∫⁻ ω, ‖f n ω‖ₑ ^ p ∂P) =
        eLpNorm (f n) (ENNReal.ofReal p) P ^ p := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top (hf n),
      ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul,
      one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one]
  have hmeas (n : ℕ) :
      AEMeasurable (fun ω => ‖f n ω‖ₑ ^ p) P :=
    (hf n).enorm.pow_const p
  have hint :
      (∫⁻ ω, (∑' n : ℕ, ‖f n ω‖ₑ ^ p) ∂P) ≠ ∞ := by
    rw [lintegral_tsum hmeas]
    simpa only [hpow] using hsum
  have hfinite :
      ∀ᵐ ω ∂P, (∑' n : ℕ, ‖f n ω‖ₑ ^ p) < ∞ :=
    ae_lt_top' (AEMeasurable.tsum hmeas) hint
  have hnorm_toReal (x : ℝ) :
      (‖x‖ₑ).toReal = ‖x‖ := by
    rw [← ofReal_norm,
      ENNReal.toReal_ofReal (norm_nonneg x)]
  filter_upwards [hfinite] with ω hω
  have hpower :
      Tendsto (fun n => ‖f n ω‖ₑ ^ p) atTop
        (𝓝 (0 : ℝ≥0∞)) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  have hroot :
      Tendsto (fun n => (‖f n ω‖ₑ ^ p) ^ (p⁻¹)) atTop
        (𝓝 ((0 : ℝ≥0∞) ^ (p⁻¹))) :=
    (ENNReal.continuous_rpow_const.tendsto (0 : ℝ≥0∞)).comp hpower
  have henorm :
      Tendsto (fun n => ‖f n ω‖ₑ) atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [← ENNReal.rpow_mul, mul_inv_cancel₀ hp.ne',
      ENNReal.rpow_one, ENNReal.zero_rpow_of_pos (inv_pos.mpr hp)]
      using hroot
  have htoReal :
      Tendsto (fun n => (‖f n ω‖ₑ).toReal) atTop
        (𝓝 ((0 : ℝ≥0∞).toReal)) :=
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp henorm
  have hnorm :
      Tendsto (fun n => ‖f n ω‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hnorm_toReal, ENNReal.toReal_zero] using htoReal
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

lemma aux_geometric_rpow_tsum_ne_top
    (C b p : ℝ)
    (hC : 0 ≤ C) (hb : 0 < b) (hp : 0 < p) :
    (∑' n : ℕ,
      ENNReal.ofReal
        (C * (3 : ℝ) ^ (-(b * (n : ℝ)))) ^ p) ≠ ∞ := by
  let r : ℝ := (3 : ℝ) ^ (-(b * p))
  have hthree : (0 : ℝ) ≤ 3 := by
    norm_num
  have hr_nonneg : 0 ≤ r :=
    Real.rpow_nonneg hthree _
  have hr_lt_one : r < 1 := by
    dsimp only [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (neg_lt_zero.mpr (mul_pos hb hp))
  have hs : Summable (fun n : ℕ => C ^ p * r ^ n) :=
    (summable_geometric_of_lt_one hr_nonneg hr_lt_one).mul_left (C ^ p)
  have hbase (n : ℕ) :
      ((3 : ℝ) ^ (-(b * (n : ℝ)))) ^ p = r ^ n := by
    calc
      ((3 : ℝ) ^ (-(b * (n : ℝ)))) ^ p =
          (3 : ℝ) ^ ((-(b * (n : ℝ))) * p) :=
        (Real.rpow_mul hthree _ _).symm
      _ = (3 : ℝ) ^ ((-(b * p)) * (n : ℝ)) := by
        congr 1
        ring
      _ = r ^ n := by
        dsimp only [r]
        exact Real.rpow_mul_natCast hthree (-(b * p)) n
  have heq (n : ℕ) :
      ENNReal.ofReal
          (C * (3 : ℝ) ^ (-(b * (n : ℝ)))) ^ p =
        ENNReal.ofReal (C ^ p * r ^ n) := by
    have hnonneg :
        0 ≤ (3 : ℝ) ^ (-(b * (n : ℝ))) :=
      Real.rpow_nonneg hthree _
    rw [ENNReal.ofReal_rpow_of_nonneg
        (mul_nonneg hC hnonneg) hp.le,
      Real.mul_rpow hC hnonneg, hbase n]
  have hts :
      (∑' n : ℕ,
        ENNReal.ofReal
          (C * (3 : ℝ) ^ (-(b * (n : ℝ)))) ^ p) =
        ENNReal.ofReal (∑' n : ℕ, C ^ p * r ^ n) := by
    calc
      (∑' n : ℕ,
          ENNReal.ofReal
            (C * (3 : ℝ) ^ (-(b * (n : ℝ)))) ^ p) =
          ∑' n : ℕ, ENNReal.ofReal (C ^ p * r ^ n) :=
        tsum_congr heq
      _ = ENNReal.ofReal (∑' n : ℕ, C ^ p * r ^ n) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun n =>
            mul_nonneg (Real.rpow_nonneg hC p) (pow_nonneg hr_nonneg n))
          hs).symm
  rw [hts]
  exact ENNReal.ofReal_ne_top

lemma aux_ae_tendsto_zero_of_geometric
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    (p b C : ℝ)
    (hp : 0 < p) (hb : 0 < b) (hC : 0 ≤ C)
    (f : ℕ → Ω → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) P)
    (herr : ∀ n,
      eLpNorm (f n) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal
          (C * (3 : ℝ) ^ (-(b * (n : ℝ))))) :
    ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (0 : ℝ)) := by
  have hsum_le :
      (∑' n : ℕ, eLpNorm (f n) (ENNReal.ofReal p) P ^ p) ≤
        ∑' n : ℕ,
          ENNReal.ofReal
            (C * (3 : ℝ) ^ (-(b * (n : ℝ)))) ^ p :=
    ENNReal.tsum_le_tsum
      (fun n => ENNReal.rpow_le_rpow (herr n) hp.le)
  have hsum :
      (∑' n : ℕ, eLpNorm (f n) (ENNReal.ofReal p) P ^ p) ≠ ∞ :=
    ne_top_of_le_ne_top
      (aux_geometric_rpow_tsum_ne_top C b p hC hb hp)
      hsum_le
  exact aux_ae_tendsto_zero_of_eLpNorm_rpow_tsum P p hp f hf hsum

lemma aux_exists_measurable_full_measure_of_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (property : Ω → Prop)
    (hproperty : ∀ᵐ ω ∂P, property ω) :
    ∃ S : Set Ω, MeasurableSet S ∧ P S = 1 ∧
      ∀ ω ∈ S, property ω := by
  classical
  let N : Set Ω := {ω | ¬ property ω}
  have hN : P N = 0 :=
    ae_iff.mp hproperty
  refine ⟨(toMeasurable P N)ᶜ,
    (measurableSet_toMeasurable P N).compl, ?_, ?_⟩
  · rw [prob_compl_eq_one_sub (measurableSet_toMeasurable P N),
      measure_toMeasurable, hN, tsub_zero]
  · intro ω hω
    by_contra hnot
    change ω ∉ toMeasurable P N at hω
    have hNω : ω ∈ N := hnot
    exact hω (subset_toMeasurable P N hNω)

/--
The common-version step in the proof of `mfd:lem-witness` (`mfd:lem-witness`).

The index type is required to be countable because the source takes one
probability-one carrier simultaneously for all catalogue coordinates,
observation indices, and finite tests.  The limit is a conclusion of the
geometric band error and is not supplied as a hypothesis.  Ambient a.e.
measurability of the band representatives is carried explicitly so the
probability-one carrier can be chosen measurable.

Tick list:

* `p`, `a`, `Cp`, and `eta` precede the countable family and carry the
  positive rate data used by the geometric error estimate;
* the only quantitative input is the band error supplied by `lem_band`,
  with the exact factor `Cp * eta * 3^(-a H)`;
* every coordinate has an ambient a.e. measurable band representative;
* the countable intersection and the pointwise geometric-band limit are
  conclusions;
* the output is one measurable full-measure set, suitable for the prefix and
  finite-test cover children;
* this is a fine proof-step refinement of `lem_witness`, not a restatement of
  its witness conclusion. The proof constructs the common measurable event
  and the coordinate limits from the geometric band error.
-/
theorem lem_witness_common_ae_limit
    (Ω : Type*) [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Type*) [Countable Q]
    (p a Cp eta : ℝ)
    (hp : 2 ≤ p) (ha : 0 < a) (hCp : 0 < Cp) (heta : 0 < eta)
    (Y : Q → Ω → ℝ)
    (Yb : Q → ℕ → Ω → ℝ)
    (hY : ∀ q, MemLp (Y q) (ENNReal.ofReal p) P)
    (hYb : ∀ q H, AEStronglyMeasurable (Yb q H) P)
    (herr : ∀ q H,
      eLpNorm (fun om => Y q om - Yb q H om)
          (ENNReal.ofReal p) P ≤
        ENNReal.ofReal
          (Cp * eta * (3 : ℝ) ^ (-(a * (H : ℝ))))) :
    ∃ Sigma : Set Ω, MeasurableSet Sigma ∧ P Sigma = 1 ∧
      ∀ q ω, ω ∈ Sigma →
        Tendsto (fun H => Yb q H ω) atTop (𝓝 (Y q ω)) := by
  have hp0 : 0 < p :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hp
  have hq (q : Q) :
      ∀ᵐ ω ∂P,
        Tendsto (fun H => Yb q H ω) atTop (𝓝 (Y q ω)) := by
    have hzero :
        ∀ᵐ ω ∂P,
          Tendsto (fun H => Y q ω - Yb q H ω) atTop
            (𝓝 (0 : ℝ)) :=
      aux_ae_tendsto_zero_of_geometric P p a (Cp * eta)
        hp0 ha (mul_pos hCp heta).le
        (fun H ω => Y q ω - Yb q H ω)
        (fun H => (hY q).aestronglyMeasurable.sub (hYb q H))
        (herr q)
    filter_upwards [hzero] with ω hω
    have ht :
        Tendsto (fun H => Y q ω - (Y q ω - Yb q H ω)) atTop
          (𝓝 (Y q ω - 0)) :=
      tendsto_const_nhds.sub hω
    simpa using ht
  have hall :
      ∀ᵐ ω ∂P, ∀ q,
        Tendsto (fun H => Yb q H ω) atTop (𝓝 (Y q ω)) :=
    ae_all_iff.mpr hq
  obtain ⟨Sigma, hSigma, hPSigma, hSigmaProp⟩ :=
    aux_exists_measurable_full_measure_of_ae P
      (fun ω => ∀ q,
        Tendsto (fun H => Yb q H ω) atTop (𝓝 (Y q ω)))
      hall
  exact ⟨Sigma, hSigma, hPSigma, fun q ω hω => hSigmaProp ω hω q⟩

end SubdiffusiveProcess.Paper
