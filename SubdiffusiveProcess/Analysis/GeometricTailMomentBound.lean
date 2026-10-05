module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import SubdiffusiveProcess.Analysis.RpowMomentBound

@[expose] public section

/-!
# Model-uniform geometric-tail moment bounds

A layer-cake tail sum gives a model-uniform `L^p` moment bound for `3^{t1·L}`,
where `L` is a `Sreg.prefixLen`-type random prefix length. The worst case is
at the upper disorder threshold `delta0`. The probabilistic and real-analytic
lemmas take the tail bound as an explicit hypothesis, with the shape of
`in_6_16`'s `tail` field, and avoid the `exp(κ)` factor of a Chernoff bound.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess

/-- The geometric-decay ratio `3^s · exp(-(1-alpha)²/(C·delta²·|log delta|))` tends to `0` as
`delta → 0⁺`, for any fixed `C > 0`, `alpha < 1`, `s : ℝ`. Key ingredient:
`tendsto_log_mul_rpow_nhdsGT_zero` (`log x * x^r → 0` as `x → 0⁺`, `r > 0`), applied at `r = 2`. -/
theorem tendsto_geometricRatio_nhdsGT_zero (C alpha s : ℝ) (hC : 0 < C) (halpha1 : alpha < 1) :
    Tendsto (fun delta : ℝ => (3 : ℝ) ^ s *
        Real.exp (-((1 - alpha) ^ 2 / (C * delta ^ 2 * |Real.log delta|))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h1malpha : 0 < (1 - alpha) ^ 2 := by
    have h1a : (1:ℝ) - alpha ≠ 0 := sub_ne_zero.mpr (ne_of_lt halpha1).symm
    positivity
  have hlogmul : Tendsto (fun x : ℝ => Real.log x * x ^ (2 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0:ℝ) < 2)
  have hf : Tendsto (fun x : ℝ => x ^ 2 * |Real.log x|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have heq : (fun x : ℝ => x ^ 2 * |Real.log x|) =ᶠ[𝓝[>] (0 : ℝ)] fun x => -(Real.log x * x ^ 2) := by
      filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with x hx
      rw [abs_of_neg (Real.log_neg hx.1 hx.2)]
      ring
    rw [Filter.tendsto_congr' heq]
    simpa using hlogmul.neg
  have hCf : Tendsto (fun x : ℝ => C * (x ^ 2 * |Real.log x|)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hf.const_mul C
  have hCfpos : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), 0 < C * (x ^ 2 * |Real.log x|) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with x hx
    have hx0 : (0:ℝ) < x := hx.1
    have hlogne : Real.log x ≠ 0 := ne_of_lt (Real.log_neg hx.1 hx.2)
    have hlogabs : (0:ℝ) < |Real.log x| := abs_pos.mpr hlogne
    positivity
  have hCf_within : Tendsto (fun x : ℝ => C * (x ^ 2 * |Real.log x|)) (𝓝[>] (0 : ℝ))
      (𝓝[>] (0 : ℝ)) := by
    rw [nhdsWithin, Filter.tendsto_inf, Filter.tendsto_principal]
    exact ⟨hCf, hCfpos⟩
  have hinv : Tendsto (fun x : ℝ => (C * (x ^ 2 * |Real.log x|))⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero.comp hCf_within
  have hmul : Tendsto (fun x : ℝ => (1 - alpha) ^ 2 * (C * (x ^ 2 * |Real.log x|))⁻¹)
      (𝓝[>] (0 : ℝ)) atTop :=
    Filter.Tendsto.const_mul_atTop h1malpha hinv
  have hneg : Tendsto (fun x : ℝ => -((1 - alpha) ^ 2 * (C * (x ^ 2 * |Real.log x|))⁻¹))
      (𝓝[>] (0 : ℝ)) atBot :=
    tendsto_neg_atTop_atBot.comp hmul
  have hexp : Tendsto (fun x : ℝ =>
      Real.exp (-((1 - alpha) ^ 2 * (C * (x ^ 2 * |Real.log x|))⁻¹))) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hrewrite : ∀ x : ℝ, -((1 - alpha) ^ 2 / (C * x ^ 2 * |Real.log x|)) =
      -((1 - alpha) ^ 2 * (C * (x ^ 2 * |Real.log x|))⁻¹) := by
    intro x
    rw [div_eq_mul_inv, mul_assoc]
  simp_rw [hrewrite]
  simpa using hexp.const_mul ((3:ℝ) ^ s)

/-- `delta0`, chosen so the geometric-decay ratio is `≤ 1/2` for EVERY `delta ∈ (0, delta0]`
(not just at `delta0` itself — extracted directly from the filter basis of `𝓝[>] 0`, so no
separate monotonicity-of-`delta²|log delta|` lemma is needed). -/
theorem exists_delta0_geometricRatio_le_half (C alpha s : ℝ) (hC : 0 < C) (halpha1 : alpha < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
        (3 : ℝ) ^ s * Real.exp (-((1 - alpha) ^ 2 / (C * delta ^ 2 * |Real.log delta|))) ≤
          1 / 2 := by
  have htend := tendsto_geometricRatio_nhdsGT_zero C alpha s hC halpha1
  have h1 : ∀ᶠ delta : ℝ in 𝓝[>] (0 : ℝ),
      (3 : ℝ) ^ s * Real.exp (-((1 - alpha) ^ 2 / (C * delta ^ 2 * |Real.log delta|))) < 1 / 2 :=
    htend.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1/2))
  obtain ⟨i, hi0, hi⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp h1
  refine ⟨i / 2, by linarith, fun delta hdelta0 hdeltale =>
    (hi (Set.mem_Ioo.mpr ⟨hdelta0, by linarith⟩)).le⟩

/-- Exact telescoping identity, `c^n = 1 + Σ_{k<n} (c^{k+1}-c^k)`. -/
theorem pow_eq_one_add_sum_diff (c : ℝ) (n : ℕ) :
    c ^ n = 1 + ∑ k ∈ Finset.range n, (c ^ (k + 1) - c ^ k) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ← add_assoc, ← ih]; ring

/-- Pointwise bound `c^n ≤ 1 + Σ_{k<n} c^{k+1}` for `c ≥ 1` (dropping the negative `-c^k` term
from the telescoping identity, using `c^k ≥ 0`). -/
theorem pow_le_one_add_sum_succ (c : ℝ) (hc : 1 ≤ c) (n : ℕ) :
    c ^ n ≤ 1 + ∑ k ∈ Finset.range n, c ^ (k + 1) := by
  rw [pow_eq_one_add_sum_diff c n]
  gcongr with k _
  have : (0:ℝ) ≤ c ^ k := by positivity
  linarith

/-- The layer-cake tail-sum bound: a nonnegative-integer-valued random variable's `c^L` moment
(`c ≥ 1`) is controlled by a `Σ' c^{k+1} · P(k < L)` series, given any upper bound `tailBound` on
the tail probabilities. Pure measure theory, no probabilistic content beyond `lintegral_tsum`
(Tonelli for a series of nonnegative functions) and the pointwise telescoping bound above. -/
theorem lintegral_pow_le_of_tail_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (L : Ω → ℕ) (hL : Measurable L) (c : ℝ) (hc : 1 ≤ c)
    (tailBound : ℕ → ℝ≥0∞) (htail : ∀ k : ℕ, P {om | k < L om} ≤ tailBound k) :
    ∫⁻ om, ENNReal.ofReal (c ^ (L om)) ∂P ≤
      1 + ∑' k : ℕ, ENNReal.ofReal (c ^ (k + 1)) * tailBound k := by
  have hc0 : (0:ℝ) ≤ c := by linarith
  have hmeasSet : ∀ k : ℕ, MeasurableSet {om : Ω | k < L om} := fun k =>
    hL measurableSet_Ioi
  have hpointwise : ∀ om, ENNReal.ofReal (c ^ (L om)) ≤
      1 + ∑' k : ℕ, {om' : Ω | k < L om'}.indicator (fun _ => ENNReal.ofReal (c ^ (k + 1))) om := by
    intro om
    have hb := pow_le_one_add_sum_succ c hc (L om)
    have hstep1 : ENNReal.ofReal (c ^ (L om)) ≤
        ENNReal.ofReal (1 + ∑ k ∈ Finset.range (L om), c ^ (k + 1)) :=
      ENNReal.ofReal_le_ofReal hb
    have hstep2 : ENNReal.ofReal (1 + ∑ k ∈ Finset.range (L om), c ^ (k + 1)) =
        1 + ∑ k ∈ Finset.range (L om), ENNReal.ofReal (c ^ (k + 1)) := by
      rw [ENNReal.ofReal_add (by norm_num) (Finset.sum_nonneg (fun k _ => pow_nonneg hc0 _)),
        ENNReal.ofReal_sum_of_nonneg (fun k _ => pow_nonneg hc0 _), ENNReal.ofReal_one]
    have hcongr : (∑ k ∈ Finset.range (L om), ENNReal.ofReal (c ^ (k + 1))) =
        ∑ k ∈ Finset.range (L om), {om' : Ω | k < L om'}.indicator
          (fun _ => ENNReal.ofReal (c ^ (k + 1))) om := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [Set.indicator_of_mem (by simpa using hk)]
    have hstep3 : (∑ k ∈ Finset.range (L om), ENNReal.ofReal (c ^ (k + 1))) =
        ∑' k : ℕ, {om' : Ω | k < L om'}.indicator (fun _ => ENNReal.ofReal (c ^ (k + 1))) om := by
      rw [hcongr]
      exact (tsum_eq_sum (fun k hk => Set.indicator_of_notMem (by simpa using hk) _)).symm
    calc ENNReal.ofReal (c ^ (L om)) ≤
          1 + ∑ k ∈ Finset.range (L om), ENNReal.ofReal (c ^ (k + 1)) := hstep2 ▸ hstep1
      _ = 1 + ∑' k : ℕ, {om' : Ω | k < L om'}.indicator (fun _ => ENNReal.ofReal (c ^ (k + 1))) om :=
          by rw [hstep3]
  calc ∫⁻ om, ENNReal.ofReal (c ^ (L om)) ∂P
      ≤ ∫⁻ om, (1 + ∑' k : ℕ, {om' : Ω | k < L om'}.indicator
          (fun _ => ENNReal.ofReal (c ^ (k + 1))) om) ∂P := lintegral_mono hpointwise
    _ = (∫⁻ _om, (1 : ℝ≥0∞) ∂P) + ∫⁻ om, ∑' k : ℕ, {om' : Ω | k < L om'}.indicator
          (fun _ => ENNReal.ofReal (c ^ (k + 1))) om ∂P :=
        lintegral_add_left measurable_const _
    _ = 1 + ∑' k : ℕ, ∫⁻ om, {om' : Ω | k < L om'}.indicator
          (fun _ => ENNReal.ofReal (c ^ (k + 1))) om ∂P := by
        rw [lintegral_const, measure_univ, mul_one,
          lintegral_tsum (fun k => (measurable_const.indicator (hmeasSet k)).aemeasurable)]
    _ = 1 + ∑' k : ℕ, ENNReal.ofReal (c ^ (k + 1)) * P {om | k < L om} := by
        congr 1
        exact tsum_congr (fun k => lintegral_indicator_const (hmeasSet k) _)
    _ ≤ 1 + ∑' k : ℕ, ENNReal.ofReal (c ^ (k + 1)) * tailBound k := by
        gcongr with k
        exact htail k

/-- **Geometric-tail closure** : given the ratio bound
`c · exp(-A) ≤ 1/2`, the series `Σ' c^{k+1}·C·exp(-A·max(k-C,0))` — the shape
`aux_aux_macro_moment_bank_per_model_bd`'s `hX` step builds, via a Chernoff-style route that
introduces a spurious `exp(κ)`-blowup — is bounded by an EXPLICIT, `A`-independent constant
(depending only on `C`, `c`, via `N0 := ⌈C⌉₊`). No case split on the SIZE of `A` is needed: the
worst case sits exactly at the ratio threshold, matching every other `_uniform` twin's recipe. -/
theorem tsum_geometricTail_le (c C A : ℝ) (hc1 : 1 ≤ c) (hC1 : 1 ≤ C) (hA0 : 0 ≤ A)
    (hratio : c * Real.exp (-A) ≤ 1 / 2) :
    ∑' k : ℕ, ENNReal.ofReal (c ^ (k + 1)) *
        ENNReal.ofReal (C * Real.exp (-(A * max ((k : ℝ) - C) 0))) ≤
      ENNReal.ofReal (C * c ^ (Nat.ceil C) * (Nat.ceil C : ℝ) + 2 * C * c ^ (Nat.ceil C + 1)) := by
  set N0 : ℕ := Nat.ceil C with hN0def
  set q0 : ℝ := c * Real.exp (-A) with hq0def
  have hq0nonneg : (0:ℝ) ≤ q0 := by positivity
  have hCN0 : C ≤ (N0 : ℝ) := Nat.le_ceil C
  set dom1 : ℕ → ℝ≥0∞ := fun k => if k < N0 then ENNReal.ofReal (C * c ^ N0) else 0 with hdom1def
  set dom2 : ℕ → ℝ≥0∞ := fun k =>
    if k < N0 then 0 else ENNReal.ofReal (C * c ^ (N0 + 1)) * ENNReal.ofReal q0 ^ (k - N0)
    with hdom2def
  have hterm : ∀ k : ℕ, ENNReal.ofReal (c ^ (k + 1)) *
      ENNReal.ofReal (C * Real.exp (-(A * max ((k : ℝ) - C) 0))) ≤ dom1 k + dom2 k := by
    intro k
    by_cases hk : k < N0
    · have h1 : (0:ℝ) ≤ A * max ((k:ℝ) - C) 0 := by positivity
      have h2 : Real.exp (-(A * max ((k:ℝ) - C) 0)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; linarith
      have h3 : C * Real.exp (-(A * max ((k:ℝ) - C) 0)) ≤ C := by nlinarith
      have h4 : c ^ (k + 1) ≤ c ^ N0 := pow_le_pow_right₀ hc1 (by omega)
      have h3' : ENNReal.ofReal (C * Real.exp (-(A * max ((k:ℝ) - C) 0))) ≤ ENNReal.ofReal C :=
        ENNReal.ofReal_le_ofReal h3
      have h4' : ENNReal.ofReal (c ^ (k + 1)) ≤ ENNReal.ofReal (c ^ N0) :=
        ENNReal.ofReal_le_ofReal h4
      have hbound : ENNReal.ofReal (c ^ (k + 1)) *
          ENNReal.ofReal (C * Real.exp (-(A * max ((k:ℝ) - C) 0))) ≤
          ENNReal.ofReal (C * c ^ N0) := by
        calc ENNReal.ofReal (c ^ (k + 1)) *
                ENNReal.ofReal (C * Real.exp (-(A * max ((k:ℝ) - C) 0)))
            ≤ ENNReal.ofReal (c ^ N0) * ENNReal.ofReal C := by gcongr
          _ = ENNReal.ofReal (C * c ^ N0) := by rw [← ENNReal.ofReal_mul (by positivity)]; ring_nf
      simp only [hdom1def, hdom2def, ite_eq_left hk, add_zero]
      exact hbound
    · push Not at hk
      have hCk : C ≤ (k : ℝ) := hCN0.trans (by exact_mod_cast hk)
      have hmax : max ((k:ℝ) - C) 0 = (k:ℝ) - C := max_eq_left (by linarith)
      have hmaxge : (k:ℝ) - C ≥ (k:ℝ) - (N0:ℝ) := by linarith
      have hexple : Real.exp (-(A * max ((k:ℝ) - C) 0)) ≤ Real.exp (-(A * ((k:ℝ) - (N0:ℝ)))) := by
        rw [hmax]
        apply Real.exp_le_exp.mpr
        nlinarith
      have hkN0R : (k:ℝ) - (N0:ℝ) = ((k - N0 : ℕ) : ℝ) := (Nat.cast_sub hk).symm
      have hpoweq : c ^ (k + 1) = c ^ (N0 + 1) * c ^ (k - N0) := by
        rw [← pow_add]; congr 1; omega
      have hexpeq : Real.exp (-(A * ((k - N0 : ℕ) : ℝ))) = Real.exp (-A) ^ (k - N0) := by
        rw [← Real.exp_nat_mul]; ring_nf
      have hbound : ENNReal.ofReal (c ^ (k + 1)) *
          ENNReal.ofReal (C * Real.exp (-(A * max ((k:ℝ) - C) 0))) ≤
          ENNReal.ofReal (C * c ^ (N0 + 1)) * ENNReal.ofReal q0 ^ (k - N0) := by
        calc ENNReal.ofReal (c ^ (k + 1)) *
                ENNReal.ofReal (C * Real.exp (-(A * max ((k:ℝ) - C) 0)))
            ≤ ENNReal.ofReal (c ^ (k + 1)) *
                ENNReal.ofReal (C * Real.exp (-(A * ((k:ℝ) - (N0:ℝ))))) := by
              have hstep : ENNReal.ofReal (C * Real.exp (-(A * max ((k:ℝ) - C) 0))) ≤
                  ENNReal.ofReal (C * Real.exp (-(A * ((k:ℝ) - (N0:ℝ))))) :=
                ENNReal.ofReal_le_ofReal (by nlinarith [hexple])
              gcongr
          _ = ENNReal.ofReal (c ^ (N0 + 1) * c ^ (k - N0)) *
                ENNReal.ofReal (C * Real.exp (-A) ^ (k - N0)) := by
              rw [hpoweq, hkN0R, hexpeq]
          _ = ENNReal.ofReal (C * c ^ (N0 + 1)) * ENNReal.ofReal q0 ^ (k - N0) := by
              rw [← ENNReal.ofReal_pow hq0nonneg,
                ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ c ^ (N0+1) * c ^ (k - N0)),
                ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ C * c ^ (N0+1))]
              congr 1
              rw [hq0def]
              ring
      simp only [hdom1def, hdom2def, ite_eq_right (not_lt.mpr hk), zero_add]
      exact hbound
  have hdom1sum : ∑' k : ℕ, dom1 k = ENNReal.ofReal (C * c ^ N0 * (N0 : ℝ)) := by
    have h1 : ∑' k : ℕ, dom1 k = ∑ k ∈ Finset.range N0, dom1 k :=
      tsum_eq_sum (fun k hk => ite_eq_right (by simpa using hk))
    rw [h1]
    simp only [hdom1def]
    rw [Finset.sum_congr rfl (fun k hk => ite_eq_left (by simpa using hk)), Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity)]
    ring_nf
  have hdom2sum : ∑' k : ℕ, dom2 k = ENNReal.ofReal (C * c ^ (N0 + 1)) * ∑' j : ℕ,
      ENNReal.ofReal q0 ^ j := by
    have hinj : Function.Injective (fun j : ℕ => N0 + j) := add_right_injective N0
    have hsupp : Function.support dom2 ⊆ Set.range (fun j : ℕ => N0 + j) := by
      intro k hk
      simp only [hdom2def, Function.mem_support, ne_eq] at hk
      by_contra hcon
      rw [Set.mem_range] at hcon
      push Not at hcon
      apply hk
      have hklt : k < N0 := by
        by_contra hge
        push Not at hge
        exact hcon (k - N0) (by omega)
      exact ite_eq_left hklt
    rw [← Function.Injective.tsum_eq hinj hsupp]
    have heq : ∀ j : ℕ, dom2 (N0 + j) =
        ENNReal.ofReal (C * c ^ (N0 + 1)) * ENNReal.ofReal q0 ^ j := by
      intro j
      simp only [hdom2def, ite_eq_right (show ¬ N0 + j < N0 by omega)]
      congr 2
      omega
    simp_rw [heq]
    exact ENNReal.tsum_mul_left
  have hgeomsum : ∑' j : ℕ, ENNReal.ofReal q0 ^ j ≤ 2 := by
    have hle : ENNReal.ofReal q0 ≤ ENNReal.ofReal (1/2 : ℝ) := ENNReal.ofReal_le_ofReal hratio
    calc ∑' j : ℕ, ENNReal.ofReal q0 ^ j ≤ ∑' j : ℕ, ENNReal.ofReal (1/2 : ℝ) ^ j := by
          gcongr
      _ = (1 - ENNReal.ofReal (1/2 : ℝ))⁻¹ := ENNReal.tsum_geometric _
      _ = 2 := by
          have h1 : (1:ℝ≥0∞) - ENNReal.ofReal (1/2 : ℝ) = ENNReal.ofReal (1/2 : ℝ) := by
            rw [show (1:ℝ≥0∞) = ENNReal.ofReal 1 from (ENNReal.ofReal_one).symm,
              ← ENNReal.ofReal_sub _ (by norm_num : (0:ℝ) ≤ 1/2)]
            norm_num
          rw [h1, ← ENNReal.ofReal_inv_of_pos (show (0:ℝ) < 1/2 by norm_num)]
          norm_num
  calc ∑' k : ℕ, ENNReal.ofReal (c ^ (k + 1)) *
        ENNReal.ofReal (C * Real.exp (-(A * max ((k : ℝ) - C) 0)))
      ≤ ∑' k : ℕ, (dom1 k + dom2 k) := ENNReal.tsum_le_tsum hterm
    _ = ∑' k : ℕ, dom1 k + ∑' k : ℕ, dom2 k := ENNReal.tsum_add
    _ = ENNReal.ofReal (C * c ^ N0 * (N0 : ℝ)) +
          ENNReal.ofReal (C * c ^ (N0 + 1)) * ∑' j : ℕ, ENNReal.ofReal q0 ^ j := by
        rw [hdom1sum, hdom2sum]
    _ ≤ ENNReal.ofReal (C * c ^ N0 * (N0 : ℝ)) + ENNReal.ofReal (C * c ^ (N0 + 1)) * 2 := by
        gcongr
    _ = ENNReal.ofReal (C * c ^ (Nat.ceil C) * (Nat.ceil C : ℝ) + 2 * C * c ^ (Nat.ceil C + 1)) := by
        rw [← hN0def, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

/-- **Full closure**: a model-uniform `eLpNorm` bound for `3^{t1·L}` (`L` a `ℕ`-valued random
variable with a `Sreg.tail`-shaped tail bound), matching the shape
`aux_aux_macro_moment_bank_per_model_bd`'s `hX` needs — but with an EXPLICIT, `A`-independent
(hence `delta`-independent for `delta ≤ delta0`) bound, replacing `hX`'s own Chernoff-style
`exp(κ)`-blowup route entirely. `delta0`/`B` depend only on `(C, alpha, t1, p)` — NOT on the
specific model `M` (as long as `M.delta ≤ delta0`), matching every other `_uniform` twin's shape. -/
theorem exists_uniform_prefixLen_pow_eLpNorm_bound (C alpha t1 p : ℝ) (hC1 : 1 ≤ C)
    (ht10 : 0 ≤ t1) (hp1 : 1 ≤ p) (halpha1 : alpha < 1) :
    ∃ delta0 B : ℝ, 0 < delta0 ∧ 0 ≤ B ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (L : Ω → ℕ), Measurable L → ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
        (∀ k : ℕ, P {om | k < L om} ≤ ENNReal.ofReal (C * Real.exp
            (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0 / (C * delta ^ 2 * |Real.log delta|))))) →
        MemLp (fun om => (3 : ℝ) ^ (t1 * (L om : ℝ))) (ENNReal.ofReal p) P ∧
        eLpNorm (fun om => (3 : ℝ) ^ (t1 * (L om : ℝ))) (ENNReal.ofReal p) P ≤
          ENNReal.ofReal B := by
  set s : ℝ := p * t1 with hsdef
  have hs0 : 0 ≤ s := by positivity
  set c : ℝ := (3 : ℝ) ^ s with hcdef
  have hc1 : 1 ≤ c := Real.one_le_rpow (by norm_num) hs0
  set N0 : ℕ := Nat.ceil C with hN0def
  set Bser : ℝ := C * c ^ N0 * (N0 : ℝ) + 2 * C * c ^ (N0 + 1) with hBserdef
  have hBsernonneg : 0 ≤ Bser := by positivity
  obtain ⟨delta0, hdelta0pos, hratio⟩ :=
    exists_delta0_geometricRatio_le_half C alpha s (by linarith) halpha1
  refine ⟨delta0, (1 + Bser) ^ (1 / p), hdelta0pos, Real.rpow_nonneg (by linarith) _, ?_⟩
  intro Ω _ P _ L hL delta hdelta hdeltale htail
  have hA0 : (0:ℝ) ≤ (1 - alpha) ^ 2 / (C * delta ^ 2 * |Real.log delta|) := by positivity
  have hgeom := tsum_geometricTail_le c C ((1 - alpha) ^ 2 / (C * delta ^ 2 * |Real.log delta|))
    hc1 hC1 hA0 (hratio delta hdelta hdeltale)
  have htail' : ∀ k : ℕ, P {om | k < L om} ≤
      ENNReal.ofReal (C * Real.exp (-((1 - alpha) ^ 2 / (C * delta ^ 2 * |Real.log delta|) *
        max ((k : ℝ) - C) 0))) := by
    intro k
    convert htail k using 3
    ring
  have hlin := lintegral_pow_le_of_tail_bound P L hL c hc1 _ htail'
  have hlin' : ∫⁻ om, ENNReal.ofReal (c ^ (L om)) ∂P ≤ ENNReal.ofReal (1 + Bser) := by
    refine hlin.trans ?_
    rw [ENNReal.ofReal_add (by norm_num) hBsernonneg, ENNReal.ofReal_one]
    gcongr
  have hpoweq : ∀ om : Ω, ((3:ℝ) ^ (t1 * (L om:ℝ))) ^ p = c ^ (L om) := by
    intro om
    rw [← Real.rpow_natCast c (L om), hcdef, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3),
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
    congr 1
    rw [hsdef]; ring
  have hLR : Measurable fun om => (L om : ℝ) := Measurable.of_discrete.comp hL
  have hpoweq3 : ∀ x : ℝ, (3:ℝ) ^ x = Real.exp (Real.log 3 * x) := fun x =>
    Real.rpow_def_of_pos (show (0:ℝ) < 3 by norm_num) x
  have hmeasL : Measurable fun om => (3:ℝ) ^ (t1 * (L om:ℝ)) := by
    simp_rw [hpoweq3]
    exact Real.measurable_exp.comp (measurable_const.mul (measurable_const.mul hLR))
  have hmeaspow : AEStronglyMeasurable (fun om => ((3:ℝ) ^ (t1 * (L om:ℝ))) ^ p) P :=
    ((Real.continuous_rpow_const (by linarith : (0:ℝ) ≤ p)).measurable.comp
      hmeasL).aestronglyMeasurable
  have hnonneg : 0 ≤ᵐ[P] (fun om => (3:ℝ) ^ (t1 * (L om:ℝ))) :=
    Filter.Eventually.of_forall (fun om => Real.rpow_nonneg (by norm_num) _)
  have hintpow : Integrable (fun om => ((3:ℝ) ^ (t1 * (L om:ℝ))) ^ p) P := by
    have hlin'' : ∫⁻ om, ENNReal.ofReal (((3:ℝ)^(t1*(L om:ℝ)))^p) ∂P ≤ ENNReal.ofReal (1+Bser) := by
      simpa only [hpoweq] using hlin'
    refine ⟨hmeaspow, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    calc ∫⁻ om, ENNReal.ofReal ‖((3:ℝ)^(t1*(L om:ℝ)))^p‖ ∂P
        = ∫⁻ om, ENNReal.ofReal (((3:ℝ)^(t1*(L om:ℝ)))^p) ∂P := by
          congr 1; funext om
          congr 1
          rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.rpow_nonneg (by norm_num) _) _)]
      _ ≤ ENNReal.ofReal (1+Bser) := hlin''
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hboundpow : ∫ om, ((3:ℝ)^(t1*(L om:ℝ)))^p ∂P ≤ (1+Bser) := by
    have h1 : ∫ om, ((3:ℝ)^(t1*(L om:ℝ)))^p ∂P =
        (∫⁻ om, ENNReal.ofReal (((3:ℝ)^(t1*(L om:ℝ)))^p) ∂P).toReal := by
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintpow
          (Filter.Eventually.of_forall (fun om => Real.rpow_nonneg (Real.rpow_nonneg (by norm_num) _) _))]
      rw [ENNReal.toReal_ofReal (by positivity)]
    rw [h1]
    have hlin'' : ∫⁻ om, ENNReal.ofReal (((3:ℝ)^(t1*(L om:ℝ)))^p) ∂P ≤ ENNReal.ofReal (1+Bser) := by
      simpa only [hpoweq] using hlin'
    calc (∫⁻ om, ENNReal.ofReal (((3:ℝ)^(t1*(L om:ℝ)))^p) ∂P).toReal
        ≤ (ENNReal.ofReal (1+Bser)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin''
      _ = 1+Bser := ENNReal.toReal_ofReal (by positivity)
  have hBpow : ((1 + Bser) ^ (1 / p)) ^ p = 1 + Bser := by
    rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ 1 + Bser),
      one_div_mul_cancel (show p ≠ 0 by linarith), Real.rpow_one]
  have hboundpow' : ∫ om, ((3:ℝ)^(t1*(L om:ℝ)))^p ∂P ≤ ((1 + Bser) ^ (1 / p)) ^ p := by
    rw [hBpow]; exact hboundpow
  have hfinal := eLpNorm_le_ofReal_of_rpow_integral_le hnonneg p (by linarith) hintpow
    ((1 + Bser) ^ (1 / p)) (Real.rpow_nonneg (by linarith) _) hboundpow'
  exact ⟨lt_of_le_of_lt hfinal ENNReal.ofReal_lt_top, hfinal⟩

end SubdiffusiveProcess
